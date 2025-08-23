from flask import Flask, request, jsonify, abort, Response, redirect
from datetime import datetime, timedelta
from dataclasses import dataclass
from typing import List, Dict, Tuple, Optional
from googleapiclient.discovery import build
from google.oauth2.credentials import Credentials as UserCredentials
from google_auth_oauthlib.flow import Flow
from google.auth.transport.requests import Request as GoogleRequest
from google.cloud import storage
import pandas as pd
import json
import os
import io
import csv
import hmac
import hashlib
import base64
import time
app = Flask(__name__)
# ========= Config =========
USER_TZ = os.getenv("USER_TZ", "Asia/Tokyo")  # 例: "Asia/Tokyo"
TZ_OFFSET = os.getenv("TZ_OFFSET", "+09:00")  # 例: "+09:00"
API_KEY = os.getenv("API_KEY", "")
MAX_REQUEST_SIZE = 102400
# OAuth config (必須)
OAUTH_CLIENT_ID = os.getenv("OAUTH_CLIENT_ID", "")
OAUTH_CLIENT_SECRET = os.getenv("OAUTH_CLIENT_SECRET", "")
BASE_URL = os.getenv("BASE_URL", "https://gpts-api-v2-668935029487.asia-northeast1.run.app")  # 例: https://gpts-api-xxxxx-yyy.a.run.app
OAUTH_REDIRECT_PATH = os.getenv("OAUTH_REDIRECT_PATH", "/oauth/callback")
APP_SECRET = os.getenv("APP_SECRET", "")  # ランダム長文字列
# 保存先バケット（必須）
TOKEN_BUCKET = os.getenv("TOKEN_BUCKET", "gpts-oauth-tokens")
BACKUP_BUCKET = os.getenv("BACKUP_BUCKET", "gpts-plans-backup")  # バックアップ用
USER_SHEET_MAP_BUCKET = "user-sheet-mapping"
USER_SHEET_MAP_BLOB = "mapping.json"
# スコープ：ユーザー本人でSheets作成/編集 & 自分が作ったファイル書き込み
SCOPES = [
    "https://www.googleapis.com/auth/spreadsheets",
    "https://www.googleapis.com/auth/drive.file",
    "https://www.googleapis.com/auth/calendar.events",
]
# ========= API Key check (OAuthエンドポイント等は免除) =========
EXEMPT_PATHS = {"/","/healthz", "/oauth/start", "/oauth/callback"}
@app.before_request
def check_api_key():
    cl = request.content_length or 0
    if cl > MAX_REQUEST_SIZE:
        abort(413, description="Payload too large")
    path = (request.path or "/").rstrip("/") or "/"
    if request.method == "OPTIONS" or path in EXEMPT_PATHS:
        return
    expected = (API_KEY or "").strip().strip('"').strip("'")
    if not expected:
        abort(500, description="Server API Key not configured")
    auth = (request.headers.get("Authorization") or "").strip()
    if not auth.lower().startswith("bearer "):
        abort(403, description="Invalid API Key")
    provided = auth[7:].strip().strip('"').strip("'")
    if not provided or not hmac.compare_digest(provided, expected):
        abort(403, description="Invalid API Key")
def token_bucket() -> storage.Bucket:
    client = storage.Client()
    return client.bucket(TOKEN_BUCKET)
# GCS helpers（安全なファイル名に）
def token_blob_path(user_id: str) -> str:
    safe = base64.urlsafe_b64encode(user_id.encode()).decode().rstrip("=")
    return f"tokens/{safe}.json"
def save_refresh_token(user_id: str, refresh_token: str):
    bucket = token_bucket()
    blob = bucket.blob(token_blob_path(user_id))
    data = {"user_id": user_id, "refresh_token": refresh_token, "updated_at": int(time.time())}
    blob.upload_from_string(json.dumps(data), content_type="application/json")
def load_refresh_token(user_id: str) -> Optional[str]:
    bucket = token_bucket()
    blob = bucket.blob(token_blob_path(user_id))
    if not blob.exists():
        return None
    data = json.loads(blob.download_as_text())
    return data.get("refresh_token")
def delete_refresh_token(user_id: str):
    bucket = token_bucket()
    blob = bucket.blob(token_blob_path(user_id))
    if blob.exists():
        blob.delete()
def load_user_credentials(user_id: str) -> Optional[UserCredentials]:
    rt = load_refresh_token(user_id)
    if not rt:
        return None
    creds = UserCredentials(
        token=None,
        refresh_token=rt,
        token_uri="https://oauth2.googleapis.com/token",
        client_id=OAUTH_CLIENT_ID,
        client_secret=OAUTH_CLIENT_SECRET,
        scopes=SCOPES,
    )
    # 必要に応じて即時リフレッシュ
    try:
        if not creds.valid:
            creds.refresh(GoogleRequest())
    except Exception:
        # 失効等 → 再連携が必要
        return None
    return creds
# ========= 追加：曜日ユーティリティ（0=Mon ... 6=Sun）=========
DAY_ABBR = ("Mon", "Tue", "Wed", "Thu", "Fri", "Sat", "Sun")
def weekday_abbr(d: datetime) -> str:
    return DAY_ABBR[d.weekday()]
def is_weekend(d: datetime) -> bool:
    return d.weekday() >= 5  # Sat=5, Sun=6
def is_rest_day(d: datetime, rest_days: List[str]) -> bool:
    # rest_days は ["Wed"] のような英略を想定
    return weekday_abbr(d) in set(rest_days)
# ========= Dataclasses / Planner =========
@dataclass
class UserSetting:
    user_id: str
    target_exam: datetime
    start_date: datetime
    weekday_minutes: int
    weekend_minutes: int
    rest_days: List[str]
    weekday_start: str
    weekend_start: str
    book_keyword: str
@dataclass
class Task:
    WBS: str
    Task_Name: str
    Date: datetime
    Duration: int
    Status: str = "未着手"
    @property
    def Day(self) -> str:
        return weekday_abbr(self.Date)
MIN1 = 10
MIN2 = 7
MIN3 = 5
def next_day(d: datetime) -> datetime:
    return d + timedelta(days=1)
def calculate_available_time(user: UserSetting, date: datetime) -> int:
    if is_rest_day(date, user.rest_days):
        return 0
    if is_weekend(date):
        return user.weekend_minutes
    return user.weekday_minutes
class StudyPlanner:
    def __init__(self, user: UserSetting, chapter_items_list: List[str]):
        self.user = user
        self.chapter_items_list = chapter_items_list
        self.tasks: List[Task] = []
        self.wbs_counter = 0
        self.last_study_date: Optional[datetime] = None
        self.first_round_tasks: List[str] = []
        self.is_short = (self.user.target_exam - self.user.start_date).days <= 31
    def add_task(self, name: str, date: datetime, minutes: int):
        task = Task(f"wbs{self.wbs_counter}", name, date, minutes)
        self.tasks.append(task)
        self.wbs_counter += 1
        if self.last_study_date is None or date > self.last_study_date:
            self.last_study_date = date
    def allocate_tasks(self, tasks: List[Tuple[str, int]], start_date: datetime):
        current_date = start_date
        while tasks:
            if current_date > self.user.target_exam:
                break
            while calculate_available_time(self.user, current_date) == 0:
                current_date = next_day(current_date)
                if current_date > self.user.target_exam:
                    break
            available = calculate_available_time(self.user, current_date)
            while tasks and available >= tasks[0][1]:
                name, dur = tasks.pop(0)
                self.add_task(name, current_date, dur)
                available -= dur
            current_date = next_day(current_date)
        self.last_study_date = current_date
        return current_date
    def step0_setup(self): self.add_task("書籍の流し読みと概要把握", self.user.start_date, self.user.weekday_minutes)
    def step1_first_round(self):
        current_date = next_day(self.last_study_date)
        while self.chapter_items_list:
            available = calculate_available_time(self.user, current_date)
            while available >= MIN1 and self.chapter_items_list:
                name = self.chapter_items_list.pop(0)
                self.first_round_tasks.append(name)
                self.add_task(name, current_date, MIN1)
                available -= MIN1
            current_date = next_day(current_date)
    def step2_second_round(self):
        tasks = [(f"(2nd) {n}", MIN2) for n in self.first_round_tasks]
        self.allocate_tasks(tasks, next_day(self.last_study_date))
    def step3_first_exam(self):
        tasks = [("過去問 2025年 (1/2)", 60), ("過去問 2025年 (2/2)", 60), ("過去問 2025年 レビュー", 60)]
        self.allocate_tasks(tasks, next_day(next_day(self.last_study_date)))
    def step4_third_round(self):
        tasks = [(f"(3rd) {n}", MIN3) for n in self.first_round_tasks]
        self.allocate_tasks(tasks, next_day(self.last_study_date))
    def step5_weekend_reviews(self):
        current_date = self.user.start_date
        while current_date <= self.last_study_date:
            if current_date == self.user.start_date:
                current_date = next_day(current_date); continue
            day = weekday_abbr(current_date)  # ← 追加
            if day == 'Sat':
                self.add_task("その週の復習", current_date, 60)
            elif day == 'Sun':
                self.add_task("アプリ演習と誤答復習", current_date, 60)
            current_date = next_day(current_date)
    def step6_refresh_days(self):
        current_date = next_day(self.last_study_date)
        for _ in range(2):
            self.add_task("リフレッシュ日", current_date, 0)
            current_date = next_day(current_date)
    def step7_past_exam_plan(self):
        # 周回対象（必要なら 2025 を追加可）
        YEARS = [2024, 2023, 2022, 2021, 2020, 2019, 2025]
        # ★ 試験日の「1日前」までに全タスクを完了（= 試験日に1日余裕）
        cutoff = self.user.target_exam - timedelta(days=1)
        start_date = next_day(self.last_study_date)
        # --- allocate_tasks のローカル版（cutoffで打ち切る） ---
        def allocate_tasks_until(tasks, start_date, cutoff_date):
            current_date = start_date
            while tasks:
                if current_date > cutoff_date:  # ★ user.target_exam ではなく cutoff を見る
                    break
                # 休養日はスキップ
                while calculate_available_time(self.user, current_date) == 0:
                    current_date = next_day(current_date)
                    if current_date > cutoff_date:
                        break
                if current_date > cutoff_date:
                    break
                available = calculate_available_time(self.user, current_date)
                while tasks and available >= tasks[0][1]:
                    name, dur = tasks.pop(0)
                    self.add_task(name, current_date, dur)
                    available -= dur
                current_date = next_day(current_date)
            # allocate後の次開始日を返す
            return current_date
        def year_tasks(y: int):
            return [
                (f"過去問 {y}年 (1/2)", 60),
                (f"過去問 {y}年 (2/2)", 60),
                (f"過去問 {y}年 レビュー", 60),
            ]
        # ---- 過去問 3 周（cutoff厳守）----
        for _round in range(3):
            if start_date > cutoff:
                break
            for y in YEARS:
                if start_date > cutoff:
                    break
                tasks = year_tasks(y)
                start_date = allocate_tasks_until(tasks, start_date, cutoff)
                # allocate中にcutoff超過で止まったら tasks が残っていても終了
                if start_date > cutoff:
                    break
            # 各周の終わりにリフレッシュ 1 日（0分）
            if (not self.is_short) and (start_date <= cutoff):
                self.add_task("リフレッシュ日", start_date, 0)
                start_date = next_day(start_date)
                
        # ---- 以降は「過去問道場ランダム」フェーズ（cutoffまで）----
        current_date = max(start_date, next_day(self.last_study_date))
        i = 1
        while current_date <= cutoff:
            if calculate_available_time(self.user, current_date) >= 60:
                self.add_task(f"過去問道場ランダム{i}", current_date, 60)
                i += 1
            current_date = next_day(current_date)
    def step8_summarize_tasks(self):
        from collections import defaultdict
        grouped = defaultdict(list)
        for t in self.tasks: grouped[t.Date].append(t)
        new_tasks = []
        for date in sorted(grouped.keys()):
            tasks_for_day = grouped[date]
            normal = [t for t in tasks_for_day if "復習" not in t.Task_Name and "アプリ演習" not in t.Task_Name]
            review = [t for t in tasks_for_day if t not in normal]
            if len(normal) == 1:
                new_tasks.extend(normal)
            elif len(normal) > 1:
                first, last = normal[0], normal[-1]
                if "(2nd)" in first.Task_Name: lbl = "【2周】"
                elif "(3rd)" in first.Task_Name: lbl = "【3周】"
                elif "過去問" not in first.Task_Name and "レビュー" not in first.Task_Name: lbl = "【1周】"
                else: lbl = ""
                def clean(n): return n.replace("(2nd) ", "").replace("(3rd) ", "")
                combined = f"{lbl} {clean(first.Task_Name)} – {clean(last.Task_Name)}".strip()
                total = sum(t.Duration for t in normal)
                new_tasks.append(Task("", combined, date, total))
            new_tasks.extend(review)
        self.tasks = []
        for i, t in enumerate(sorted(new_tasks, key=lambda x: x.Date)):
            self.tasks.append(Task(f"wbs{i}", t.Task_Name, t.Date, t.Duration))
    def step9_merge_plan(self):
        self.plan_df = pd.DataFrame([{
            "WBS": t.WBS, "Task Name": t.Task_Name, "Date": t.Date.strftime('%Y-%m-%d'),
            "Day": t.Day, "Duration": t.Duration, "Status": t.Status
        } for t in self.tasks])
        self.plan_df.sort_values(by='Date', inplace=True)
        self.plan_df.reset_index(drop=True, inplace=True)
        self.plan_df['WBS'] = [f"wbs{i}" for i in range(len(self.plan_df))]
    def run_phase1(self):
        # ★ 短期は「書籍の流し読みと概要把握」を入れない
        if not self.is_short:
            self.step0_setup()
        else:
            # step0 を飛ばすため、初日から置けるよう基準日を前日にセット
            self.last_study_date = self.user.start_date - timedelta(days=1)
        # 以降の順序はそのまま
        self.step1_first_round()
        self.step3_first_exam()
        self.step2_second_round()
        self.step5_weekend_reviews()
    def run_phase2(self):
        # ★ 短期はリフレッシュ日(step6)を挟まない。長期のみ実行
        if not self.is_short:
            self.step6_refresh_days()
        self.step7_past_exam_plan()
        self.step8_summarize_tasks()
        self.step9_merge_plan()
        
# ========= Helpers (GCS, OAuth, Sheets) =========
def required_envs_ok():
    return all([OAUTH_CLIENT_ID, OAUTH_CLIENT_SECRET, BASE_URL, APP_SECRET])
def oauth_redirect_uri() -> str:
    return f"{BASE_URL.rstrip('/')}{OAUTH_REDIRECT_PATH}"
# 置換: state (HMAC署名 + TTL)
STATE_TTL = 10 * 60  # 10分
def signed_state(user_id: str) -> str:
    ts = int(time.time())
    msg = f"{user_id}|{ts}".encode()
    sig = hmac.new(APP_SECRET.encode(), msg, hashlib.sha256).digest()
    packed = base64.urlsafe_b64encode(msg + b"|" + base64.urlsafe_b64encode(sig)).decode()
    return packed.rstrip("=")
def verify_state(state: str) -> Optional[str]:
    """
    後方互換:
      新式: base64url( user_id|ts|base64url(HMAC(user_id|ts)) ), TTLあり
      旧式: base64url( user_id . base64url(HMAC(user_id)) ), TTLなし
    """
    try:
        raw = base64.urlsafe_b64decode(state + "===")
        # --- 新フォーマット（推奨） ---
        parts = raw.split(b"|")
        if len(parts) == 3:
            user_id = parts[0].decode()
            ts = int(parts[1].decode())
            sig_b64 = parts[2]
            expected = hmac.new(APP_SECRET.encode(), f"{user_id}|{ts}".encode(), hashlib.sha256).digest()
            if hmac.compare_digest(base64.urlsafe_b64encode(expected), sig_b64):
                if time.time() - ts <= STATE_TTL:
                    return user_id
                else:
                    return None  # TTL超過
            return None
        # --- 旧フォーマット（互換用） ---
        legacy = raw.decode(errors="ignore")
        if "." in legacy:
            user_id, sig_b64 = legacy.split(".", 1)
            expected = hmac.new(APP_SECRET.encode(), user_id.encode(), hashlib.sha256).digest()
            # 旧式はTTLが無い。必要ならここで拒否する方針にしても良い。
            if hmac.compare_digest(
                base64.urlsafe_b64encode(expected).decode().rstrip("="),
                sig_b64.rstrip("=")
            ):
                return user_id
        return None
    except Exception:
        return None
def build_flow():
    client_config = {
        "web": {
            "client_id": OAUTH_CLIENT_ID,
            "client_secret": OAUTH_CLIENT_SECRET,
            "auth_uri": "https://accounts.google.com/o/oauth2/v2/auth",
            "token_uri": "https://oauth2.googleapis.com/token",
            "redirect_uris": [oauth_redirect_uri()],
        }
    }
    return Flow.from_client_config(client_config, scopes=SCOPES, redirect_uri=oauth_redirect_uri())
def expand_chapter_items(counts: List[int]) -> List[str]:
    items = []
    for idx, c in enumerate(counts):
        for j in range(1, c+1): items.append(f"Chapter {idx+1} - Item {j}")
    return items
def load_chapter_data_from_gcs(book_filename: str):
    client = storage.Client()
    bucket = client.bucket("study-book-data")
    blob = bucket.blob(book_filename)
    return json.loads(blob.download_as_text())
def get_user_sheets_service(user_id: str):
    creds = load_user_credentials(user_id)
    if not creds:
        return None
    return build("sheets", "v4", credentials=creds, cache_discovery=False)
    
# ========= Sheet I/O (ユーザーOAuthで実行) =========
def create_sheet_and_write(plan_df: pd.DataFrame, sheet_title: str, user_id: str) -> str:
    creds = load_user_credentials(user_id)
    if not creds:
        raise PermissionError("No OAuth tokens. Authorize first.")
    service = build("sheets", "v4", credentials=creds, cache_discovery=False)
    if service is None:
        raise PermissionError("No OAuth tokens. Authorize first.")
    # 新規スプレッドシート作成
    sheet = service.spreadsheets().create(
        body={"properties": {"title": sheet_title}}, fields="spreadsheetId"
    ).execute()
    spreadsheet_id = sheet.get("spreadsheetId")
    # 見出し + データ
    service.spreadsheets().values().update(
        spreadsheetId=spreadsheet_id, range="A1", valueInputOption="RAW",
        body={"values": [list(plan_df.columns)]}
    ).execute()
    service.spreadsheets().values().update(
        spreadsheetId=spreadsheet_id, range="A2", valueInputOption="RAW",
        body={"values": plan_df.values.tolist()}
    ).execute()
    # ここで実際の sheetId を取得
    meta2 = service.spreadsheets().get(spreadsheetId=spreadsheet_id).execute()
    first_sheet_id = meta2["sheets"][0]["properties"]["sheetId"]
    # 列幅調整（B列を広げる例）
    service.spreadsheets().batchUpdate(
        spreadsheetId=spreadsheet_id,
        body={
            "requests": [
                {
                    "updateDimensionProperties": {
                        "range": {
                            "sheetId": first_sheet_id,   # ← 0 ではなく実IDを使う
                            "dimension": "COLUMNS",
                            "startIndex": 1,
                            "endIndex": 2
                        },
                        "properties": {"pixelSize": 210},
                        "fields": "pixelSize"
                    }
                }
            ]
        }
    ).execute()
    # 条件付き書式：F列(Status)のみ
    try:
        requests = [
            # 完了 → 薄緑
            {
                "addConditionalFormatRule": {
                    "rule": {
                        "ranges": [{
                            "sheetId": first_sheet_id,
                            "startRowIndex": 1,      # 2行目から最終行まで
                            "startColumnIndex": 5,   # F列(0-based)
                            "endColumnIndex": 6
                        }],
                        "booleanRule": {
                            "condition": {
                                "type": "TEXT_EQ",
                                "values": [{"userEnteredValue": "完了"}]
                            },
                            "format": {
                                "backgroundColor": {"red": 0.85, "green": 0.95, "blue": 0.85}
                            }
                        }
                    },
                    "index": 0
                }
            },
            # 未完了（空でない & 完了以外） → 薄黄
            {
                "addConditionalFormatRule": {
                    "rule": {
                        "ranges": [{
                            "sheetId": first_sheet_id,
                            "startRowIndex": 1,
                            "startColumnIndex": 5,
                            "endColumnIndex": 6
                        }],
                        "booleanRule": {
                            "condition": {
                                "type": "CUSTOM_FORMULA",
                                "values": [{"userEnteredValue": '=AND($F2<>"", $F2<>"完了")'}]
                            },
                            "format": {
                                "backgroundColor": {"red": 1.0, "green": 1.0, "blue": 0.85}
                            }
                        }
                    },
                    "index": 0
                }
            }
        ]
        service.spreadsheets().batchUpdate(
            spreadsheetId=spreadsheet_id, body={"requests": requests}
        ).execute()
    except Exception as e:
        print("[警告] 条件付き書式の設定に失敗:", e)
    return spreadsheet_id
# ========= Mapping(既存) =========
def load_user_sheet_map() -> Dict[str, Dict[str, str]]:
    client = storage.Client()
    bucket = client.bucket(USER_SHEET_MAP_BUCKET)
    blob = bucket.blob(USER_SHEET_MAP_BLOB)
    if not blob.exists():
        return {}
    return json.loads(blob.download_as_text())
def save_user_sheet_map(mapping: Dict[str, Dict[str, str]]) -> None:
    client = storage.Client()
    bucket = client.bucket(USER_SHEET_MAP_BUCKET)
    blob = bucket.blob(USER_SHEET_MAP_BLOB)
    blob.upload_from_string(json.dumps(mapping, ensure_ascii=False), content_type="application/json")
def get_user_spreadsheet_id(user_id: str) -> str:
    mapping = load_user_sheet_map()
    if user_id not in mapping or "spreadsheet_id" not in mapping[user_id]:
        raise ValueError(f"spreadsheet mapping not found for user_id={user_id}")
    return mapping[user_id]["spreadsheet_id"]
def get_user_spreadsheet_url(user_id: str) -> Optional[str]:
    mapping = load_user_sheet_map()
    if user_id in mapping:
        return mapping[user_id].get("spreadsheet_url")
    return None
# ========= Plan generation =========
def generate_study_plan(data: dict, user_id: str) -> Tuple[pd.DataFrame, UserSetting]:
    user = UserSetting(
        user_id=user_id,
        target_exam=datetime.strptime(data["target_exam_date"], "%Y-%m-%d"),
        start_date=datetime.strptime(data["start_date"], "%Y-%m-%d"),
        weekday_minutes=data["weekday_minutes"],
        weekend_minutes=data["weekend_minutes"],
        rest_days=data.get("rest_days", ["Wed"]),
        weekday_start=data.get("weekday_start", "20:00"),
        weekend_start=data.get("weekend_start", "13:00"),
        book_keyword=data["book_keyword"]
    )
    chapter_items_list = data.get("chapter_items_list")
    if chapter_items_list:
        if all(isinstance(x, int) for x in chapter_items_list):
            chapter_items_list = expand_chapter_items(chapter_items_list)
    else:
        book_filename = f"{user.book_keyword}.json"
        chapter_items_list = load_chapter_data_from_gcs(book_filename)
    planner = StudyPlanner(user, chapter_items_list)
    planner.run_phase1(); planner.run_phase2()
    return planner.plan_df, user
def generate_sheet_title(user: UserSetting) -> str:
    return f"user_{user.user_id}_plan_{user.start_date.strftime('%Y%m%d')}"
# ========= Routes =========
# ルート3つとも同じ応答
@app.route("/", endpoint="root")
@app.route("/health", endpoint="health_ping")
@app.route("/healthz", endpoint="healthz_ping")
def healthz():
    return jsonify({"ok": True, "env_ready": required_envs_ok()})
@app.route("/oauth/start")
def oauth_start():
    if not required_envs_ok():
        return jsonify({"error":"OAuth env not set"}), 500
    user_id = request.args.get("user_id")
    if not user_id:
        return jsonify({"error": "user_id is required"}), 400
    flow = build_flow()
    state = signed_state(user_id)
    auth_url, _ = flow.authorization_url(
        access_type="offline",
        include_granted_scopes="true",
        prompt="consent",
        state=state
    )
    # ブラウザで開けるようリダイレクト
    return redirect(auth_url, code=302)
@app.route("/oauth/callback")
def oauth_callback():
    if not required_envs_ok():
        return "OAuth env not set", 500
    state = request.args.get("state", "")
    user_id = verify_state(state) or ""
    if not user_id:
        return "Invalid state", 400
    flow = build_flow()
    code = request.args.get("code")
    if not code:
        return "Missing code", 400
    flow.fetch_token(code=code)
    creds = flow.credentials
    rt = getattr(creds, "refresh_token", None)
    # 連続同意などでrefresh_tokenが返らない場合のケア
    if not rt:
        # 'prompt=consent' 付きだが、Google側の仕様で返らないケースあり
        # 既存保存があればOK・無ければ再連携依頼
        existing = load_refresh_token(user_id)
        if not existing:
            return Response("<h3>⚠️ refresh_tokenが取得できませんでした。もう一度お試しください。</h3>",
                            mimetype="text/html", status=400)
        return Response("<h3>✅ 連携済みです。チャットに戻って再実行してください。</h3>", mimetype="text/html")
    save_refresh_token(user_id, rt)
    return Response("<h3>✅ 連携が完了しました。チャットに戻って再実行してください。</h3>",
                    mimetype="text/html")
@app.route("/generate", methods=["POST"])
def generate_plan():
    data = request.get_json() or {}
    user_id = data.get("user_id")
    if not user_id:
        return jsonify({"error": "user_id is required"}), 400
    # ユーザーのOAuthトークンを確認（未連携は 200 + requires_auth で返す）
    user_creds = load_user_credentials(user_id)
    if not user_creds:
        if not required_envs_ok():
            return jsonify({"error": "OAuth not configured on server"}), 500
        flow = build_flow()
        auth_url, _ = flow.authorization_url(
            access_type="offline",
            include_granted_scopes="true",
            prompt="consent",
            state=signed_state(user_id)
        )
        return jsonify({
            "requires_auth": True,
            "authorize_url": auth_url,
            "message": "Please authorize via the URL, then retry the command."
        }), 200  # ★ GPTsは非2xxを例外にするため200で返す
    # ここからは認可済みフロー
    try:
        plan_df, user = generate_study_plan(data, user_id)
    except Exception as e:
        return jsonify({"error": str(e)}), 400
    sheet_title = generate_sheet_title(user)
    try:
        spreadsheet_id = create_sheet_and_write(plan_df, sheet_title, user_id)
    except PermissionError:
        # 途中でトークン失効など→再認可を促す（やはり200で返す）
        flow = build_flow()
        auth_url, _ = flow.authorization_url(
            access_type="offline",
            include_granted_scopes="true",
            prompt="consent",
            state=signed_state(user_id)
        )
        return jsonify({
            "requires_auth": True,
            "authorize_url": auth_url,
            "message": "Authorization expired. Please re-authorize via the URL, then retry."
        }), 200
    except Exception as e:
        return jsonify({"error": f"Sheets error: {e}"}), 500
    spreadsheet_url = f"https://docs.google.com/spreadsheets/d/{spreadsheet_id}"
    # mappingは任意（失敗しても進む）
    try:
        mapping = load_user_sheet_map()
        mapping[user_id] = {
            "spreadsheet_id": spreadsheet_id,
            "spreadsheet_url": spreadsheet_url
        }
        save_user_sheet_map(mapping)
    except Exception as e:
        print("[警告] mapping 保存に失敗:", e)
    return jsonify({
        "spreadsheet_id": spreadsheet_id,
        "spreadsheet_url": spreadsheet_url,
        "plan": plan_df.to_dict(orient="records")
    })
# ===== Sheets/GCS ヘルパー =====
def backup_sheet_to_gcs(user_id: str, spreadsheet_id: str, values: List[List[str]]) -> str:
    """
    現在のシート内容を CSV にして BACKUP_BUCKET に保存。
    パス: gpts-plans/{user_id}/backup/{YYYYmmdd_HHMMSS}.csv
    """
    client = storage.Client()
    bucket = client.bucket(BACKUP_BUCKET)
    ts = datetime.utcnow().strftime("%Y%m%d_%H%M%S")
    path = f"gpts-plans/{user_id}/backup/{ts}.csv"
    sio = io.StringIO()
    writer = csv.writer(sio)
    for row in values:
        writer.writerow(row)
    blob = bucket.blob(path)
    blob.upload_from_string(sio.getvalue(), content_type="text/csv")
    return f"gs://{BACKUP_BUCKET}/{path}"
def write_tasks_to_sheet(spreadsheet_id: str, plan_df: pd.DataFrame, user_id: Optional[str] = None) -> None:
    """
    plan_df を A1 から全書換え（ヘッダ + データ）。ユーザーOAuthで実行。
    """
    service = get_user_sheets_service(user_id) if user_id else None
    if service is None:
        raise PermissionError("No OAuth tokens. Authorize first.")
    # 既存内容クリア（A:F）
    service.spreadsheets().values().clear(
        spreadsheetId=spreadsheet_id,
        range="A:F"
    ).execute()
    # ヘッダ
    service.spreadsheets().values().update(
        spreadsheetId=spreadsheet_id,
        range="A1",
        valueInputOption="RAW",
        body={"values": [list(plan_df.columns)]}
    ).execute()
    # データ
    if not plan_df.empty:
        service.spreadsheets().values().update(
            spreadsheetId=spreadsheet_id,
            range="A2",
            valueInputOption="RAW",
            body={"values": plan_df.values.tolist()}
        ).execute()
def _safe_int_from_wbs(wbs: str) -> Optional[int]:
    try:
        if isinstance(wbs, str) and wbs.startswith("wbs"):
            return int(wbs[3:])
    except Exception:
        pass
    return None
def _next_wbs_id_from_column_a(a_values: List[List[str]]) -> str:
    """
    A2:A の wbs から最大値+1 を採番。存在しなければ wbs0。
    """
    max_idx = -1
    for row in a_values:
        if not row:
            continue
        n = _safe_int_from_wbs((row[0] or "").strip())
        if n is not None and n > max_idx:
            max_idx = n
    return f"wbs{max_idx + 1}"
# ===== 追加エンドポイント =====
@app.route("/regenerate", methods=["POST"])
def regenerate():
    """
    シートのバックアップ -> wbs行クリア -> 保存済み user_data.json で再生成 -> 全書換え
    保存元: gs://{BACKUP_BUCKET}/gpts-plans/{user_id}/config/user_data.json
    """
    data = request.get_json() or {}
    user_id = data.get("user_id")
    if not user_id:
        return jsonify({"error": "user_id is required"}), 400
    # mapping からID
    try:
        spreadsheet_id = get_user_spreadsheet_id(user_id)
    except ValueError as e:
        return jsonify({"error": str(e)}), 404
    # 保存済み user_data.json を取得
    try:
        client = storage.Client()
        bucket = client.bucket(BACKUP_BUCKET)
        blob = bucket.blob(f"gpts-plans/{user_id}/config/user_data.json")
        raw_data = blob.download_as_text()
        saved_data = json.loads(raw_data)
    except Exception as e:
        return jsonify({"error": f"Failed to retrieve saved user data: {str(e)}"}), 500
    # Sheets サービス（ユーザーOAuth）
    service = get_user_sheets_service(user_id)
    if service is None:
        return jsonify({"error": "Authorization required"}), 401
    # 取得 & バックアップ
    try:
        result = service.spreadsheets().values().get(
            spreadsheetId=spreadsheet_id, range="A1:F10000"
        ).execute()
        values = result.get("values", [])
        backup_path = backup_sheet_to_gcs(user_id, spreadsheet_id, values)
    except Exception as e:
        return jsonify({"error": f"Backup failed: {str(e)}"}), 500
    # wbs行クリア（ヘッダ除く）
    try:
        for i, row in enumerate(values[1:]):
            if row and len(row) > 0 and isinstance(row[0], str) and row[0].startswith("wbs"):
                row_index = i + 2
                service.spreadsheets().values().update(
                    spreadsheetId=spreadsheet_id,
                    range=f"A{row_index}:F{row_index}",
                    valueInputOption="RAW",
                    body={"values": [["" for _ in range(6)]]}
                ).execute()
    except Exception as e:
        return jsonify({"error": f"Clear rows failed: {str(e)}"}), 500
    # 再生成 & 全書換え
    try:
        plan_df, _user = generate_study_plan(saved_data, user_id)
    except Exception as e:
        return jsonify({"error": f"Regeneration failed: {str(e)}"}), 400
    try:
        write_tasks_to_sheet(spreadsheet_id, plan_df, user_id=user_id)
    except Exception as e:
        return jsonify({"error": f"Write failed: {str(e)}"}), 500
    return jsonify({"message": "Plan regenerated successfully", "backup_file": backup_path})
@app.route("/update_task", methods=["POST"])
def update_task():
    """
    指定 wbs 行の任意フィールドを更新する（複数フィールド対応）。
    単一シート前提。
    """
    data = request.get_json() or {}
    user_id = (data.get("user_id") or "").strip()
    wbs_id = (data.get("wbs_id") or "").strip()
    if not user_id or not wbs_id:
        return jsonify({"error": "user_id and wbs_id are required"}), 400
    # 単発更新か複数更新かを正規化
    updates = data.get("updates")
    if not updates:
        field = (data.get("field") or "").strip()
        value = data.get("value", "")
        if not field:
            return jsonify({"error": "Specify 'updates' or ('field' and 'value')"}), 400
        updates = {field: value}
    # WBS列は更新禁止
    if "wbs" in [k.lower() for k in updates.keys()]:
        return jsonify({"error": "Updating WBS is not allowed."}), 400
    # Spreadsheet取得
    try:
        spreadsheet_id = get_user_spreadsheet_id(user_id)
    except ValueError:
        return jsonify({"error": "spreadsheet not found"}), 404
    service = get_user_sheets_service(user_id)
    if service is None:
        return jsonify({"error": "Authorization required"}), 401
    try:
        meta = service.spreadsheets().get(spreadsheetId=spreadsheet_id).execute()
        sheet_title = meta["sheets"][0]["properties"]["title"]
    except Exception as e:
        return jsonify({"error": f"Failed to fetch sheet metadata: {str(e)}"}), 500
    # フィールド→列マッピング
    FIELD_TO_COL = {
        "task name": "B",
        "date": "C",
        "day": "D",
        "duration": "E",
        "status": "F",
    }
    # ↓正規化と検証
    normalized_updates = {}
    for k, v in updates.items():
        key_norm = k.strip().lower()
        if key_norm not in FIELD_TO_COL:
            return jsonify({"error": f"Unknown field '{k}'. Allowed: {list(FIELD_TO_COL.keys())}"}), 400
        normalized_updates[key_norm] = v
    # WBS行検索
    rng_a = f"{sheet_title}!A2:A10000"
    try:
        got = service.spreadsheets().values().get(
            spreadsheetId=spreadsheet_id, range=rng_a
        ).execute()
    except Exception as e:
        return jsonify({"error": f"Failed to read WBS column: {str(e)}"}), 500
    values = got.get("values", [])
    row_index = None
    for i, row in enumerate(values):
        if (row[0] if row else "").strip() == wbs_id:
            row_index = i + 2
            break
    if not row_index:
        return jsonify({"error": f"WBS ID '{wbs_id}' not found"}), 404
    # ↓書き込み時も小文字キーで参照
    data_updates = []
    for field_lc, new_val in normalized_updates.items():
        col = FIELD_TO_COL[field_lc]
        a1 = f"{sheet_title}!{col}{row_index}"
        data_updates.append({"range": a1, "values": [[new_val]]})
        
    try:
        service.spreadsheets().values().batchUpdate(
            spreadsheetId=spreadsheet_id,
            body={"valueInputOption": "RAW", "data": data_updates}
        ).execute()
    except Exception as e:
        return jsonify({"error": f"Update failed: {str(e)}"}), 500
    return jsonify({
        "message": "Task updated",
        "row": row_index,
        "updated_fields": list(normalized_updates.keys())
    }), 200
@app.route("/insert_task", methods=["POST"])
def insert_task():
    """
    指定された日付(必須)の位置に行を挿入し、タスクを追加する。
    その後、A列のWBSを先頭値に合わせて連番で振り直す。
    期待ペイロード例:
    {
      "user_id": "xxx",
      "task": {
        "date": "2025-08-12",   # 必須（C列: Date）
        "task": "単語だけ復習",   # 任意（B列: Task Name）
        "day": "Tue",           # 任意（D列: Day）未指定なら自動算出
        "duration": 45,         # 任意（E列: Duration）未指定/不正は60
        "status": "未着手"       # 任意（F列: Status）
      },
      "order": "asc"
    }
    並びルール（asc）: C列(Date) 昇順。同一日付は末尾。
    """
    from datetime import datetime
    def _parse_date(s):
        try:
            return datetime.strptime(s, "%Y-%m-%d").date()
        except Exception:
            return None
    data = request.get_json() or {}
    user_id = (data.get("user_id") or "").strip()
    task_in = (data.get("task") or {})
    order = (data.get("order") or "asc").lower()
    if not user_id or not task_in:
        return jsonify({"error": "user_id and task are required"}), 400
    # 列構造に合わせて取り出し
    task_txt = (task_in.get("task") or "").strip()          # B: Task Name
    date_str = (task_in.get("date") or "").strip()          # C: Date
    day_str  = (task_in.get("day")  or "").strip()          # D: Day
    duration_raw = task_in.get("duration", "")              # E: Duration（数値推奨）
    status   = (task_in.get("status") or "未着手").strip()  # F: Status
    ins_date = _parse_date(date_str)
    if not ins_date:
        return jsonify({"error": "task.date must be 'YYYY-MM-DD'"}), 400
    if not day_str:
        day_str = DAY_ABBR[ins_date.weekday()]
    try:
        duration_val = int(duration_raw)
    except Exception:
        duration_val = 60  # 既定
    # ========== Spreadsheet / Sheet ==========
    try:
        spreadsheet_id = get_user_spreadsheet_id(user_id)
    except ValueError:
        return jsonify({"error": "spreadsheet not found"}), 404
    service = get_user_sheets_service(user_id)
    if service is None:
        return jsonify({"error": "Authorization required"}), 401
    try:
        meta = service.spreadsheets().get(spreadsheetId=spreadsheet_id).execute()
        sheet = meta["sheets"][0]  # 単一シート前提
        sheet_id = sheet["properties"]["sheetId"]
        sheet_title = sheet["properties"]["title"]
    except Exception as e:
        return jsonify({"error": f"Failed to fetch sheet metadata: {str(e)}"}), 500
    # 既存データ取得（C列: Date のみで十分）
    rng_c_all = f"{sheet_title}!C2:C10000"
    try:
        res = service.spreadsheets().values().get(
            spreadsheetId=spreadsheet_id, range=rng_c_all
        ).execute()
    except Exception as e:
        return jsonify({"error": f"Failed to read existing rows: {str(e)}"}), 500
    rows = res.get("values", [])  # 各行: [C=Date]
    # ========== 挿入位置の決定（Date昇順。同日は末尾） ==========
    insert_row_1based = 2 + len(rows)  # 既定=末尾
    if order == "asc":
        for i, r in enumerate(rows):
            r_date = _parse_date((r[0] if r else "").strip())
            if not r_date:
                continue
            if ins_date < r_date:
                insert_row_1based = 2 + i
                break
    else:
        # 降順が必要ならここに実装
        pass
    # ========== 行を1行挿入 ==========
    start_idx0 = insert_row_1based - 1
    end_idx0 = start_idx0 + 1
    try:
        service.spreadsheets().batchUpdate(
            spreadsheetId=spreadsheet_id,
            body={
                "requests": [{
                    "insertDimension": {
                        "range": {
                            "sheetId": sheet_id,
                            "dimension": "ROWS",
                            "startIndex": start_idx0,
                            "endIndex": end_idx0
                        },
                        "inheritFromBefore": True
                    }
                }]
            }
        ).execute()
    except Exception as e:
        return jsonify({"error": f"Insert row failed: {str(e)}"}), 500
    # ========== 値を書き込み（B..F = Task Name, Date, Day, Duration, Status） ==========
    try:
        service.spreadsheets().values().update(
            spreadsheetId=spreadsheet_id,
            range=f"{sheet_title}!B{insert_row_1based}:F{insert_row_1based}",
            valueInputOption="RAW",
            body={"values": [[task_txt, date_str, day_str, str(duration_val), status]]}
        ).execute()
    except Exception as e:
        return jsonify({"error": f"Write values failed: {str(e)}"}), 500
    # ========== A列のWBSをふり直し ==========
    try:
        resA = service.spreadsheets().values().get(
            spreadsheetId=spreadsheet_id, range=f"{sheet_title}!A2:A10000"
        ).execute()
    except Exception as e:
        return jsonify({"error": f"Failed to read WBS column: {str(e)}"}), 500
    a_vals = resA.get("values", [])  # [["wbs0"], ["wbs1"], ...] か空
    def _wbs_start(a_first: str) -> int:
        try:
            return int((a_first or "").lower().replace("wbs", "").strip())
        except Exception:
            return 0
    start_num = _wbs_start((a_vals[0][0] if a_vals and a_vals[0] else "").strip()) if a_vals else 0
    new_wbs_col = [[f"wbs{start_num + i}"] for i in range(len(a_vals))]
    if new_wbs_col:
        try:
            service.spreadsheets().values().update(
                spreadsheetId=spreadsheet_id,
                range=f"{sheet_title}!A2:A{len(new_wbs_col)+1}",
                valueInputOption="RAW",
                body={"values": new_wbs_col}
            ).execute()
        except Exception as e:
            return jsonify({"error": f"Renumber WBS failed: {str(e)}"}), 500
    inserted_wbs = f"wbs{start_num + (insert_row_1based - 2)}"
    return jsonify({
        "message": "Task inserted",
        "inserted_row": insert_row_1based,
        "wbs": inserted_wbs
    }), 200

@app.route("/get_tasks", methods=["POST"])
def get_tasks():
    """
    A1:F を取得し、ヘッダ行をキーに配列で返す。完全空行は除外。
    """
    data = request.get_json() or {}
    user_id = data.get("user_id")
    if not user_id:
        return jsonify({"error": "user_id is required"}), 400
    try:
        spreadsheet_id = get_user_spreadsheet_id(user_id)
    except ValueError:
        return jsonify({"error": "spreadsheet not found"}), 404
    service = get_user_sheets_service(user_id)
    if service is None:
        return jsonify({"error": "Authorization required"}), 401
    result = service.spreadsheets().values().get(
        spreadsheetId=spreadsheet_id, range="A1:F10000"
    ).execute()
    values = result.get("values", [])
    if not values or len(values) < 2:
        return jsonify({"tasks": []})
    headers = values[0]
    rows = values[1:]
    tasks = [
        {headers[i]: (row[i] if i < len(row) else "") for i in range(len(headers))}
        for row in rows
        if any((c or "").strip() for c in row)
    ]
    return jsonify({"tasks": tasks})
@app.route("/delete_task", methods=["POST"])
def delete_task():
    """
    指定 wbs 行を物理削除し、その後 A列のWBSを先頭値に合わせて連番で振り直す。
    （短期: wbs1始まり / 長期: wbs0始まり に自動追従）
    単一シート前提：常に一枚目のシートを対象にする。
    """
    data = request.get_json() or {}
    user_id = (data.get("user_id") or "").strip()
    wbs_id = (data.get("wbs_id") or "").strip()
    if not user_id or not wbs_id:
        return jsonify({"error": "user_id and wbs_id are required"}), 400
    # ========== 単一シート前提でも必須：service / spreadsheet_id / sheet_id 取得 ==========
    try:
        spreadsheet_id = get_user_spreadsheet_id(user_id)
    except ValueError:
        return jsonify({"error": "spreadsheet not found"}), 404
    service = get_user_sheets_service(user_id)
    if service is None:
        return jsonify({"error": "Authorization required"}), 401
    try:
        meta = service.spreadsheets().get(spreadsheetId=spreadsheet_id).execute()
        sheet = meta["sheets"][0]                      # 一枚目のシートを使用
        sheet_id = sheet["properties"]["sheetId"]      # ← deleteDimension に必須
        sheet_title = sheet["properties"]["title"]
    except Exception as e:
        return jsonify({"error": f"Failed to fetch sheet metadata: {str(e)}"}), 500
    # ========== A列取得 ==========
    rng = f"{sheet_title}!A2:A10000"                   # 読み書きはA1表記でOK（同一シートを明示）
    try:
        result = service.spreadsheets().values().get(
            spreadsheetId=spreadsheet_id, range=rng
        ).execute()
    except Exception as e:
        return jsonify({"error": f"Failed to read values: {str(e)}"}), 500
    values = result.get("values", [])                  # [["wbs0"], ["wbs1"], ...]
    target_row_index_1based = None
    for i, row in enumerate(values):
        a = (row[0] if row else "").strip()
        if a == wbs_id:
            target_row_index_1based = i + 2           # A2 は行=2
            break
    if not target_row_index_1based:
        return jsonify({"error": "WBS ID not found"}), 404
    # ========== 物理削除（0始まり、endは非包含） ==========
    start_index_0based = target_row_index_1based - 1
    end_index_0based = target_row_index_1based
    try:
        service.spreadsheets().batchUpdate(
            spreadsheetId=spreadsheet_id,
            body={
                "requests": [{
                    "deleteDimension": {
                        "range": {
                            "sheetId": sheet_id,
                            "dimension": "ROWS",
                            "startIndex": start_index_0based,
                            "endIndex": end_index_0based
                        }
                    }
                }]
            }
        ).execute()
    except Exception as e:
        return jsonify({"error": f"Delete failed: {str(e)}"}), 500
    # ========== WBS振り直し ==========
    try:
        result2 = service.spreadsheets().values().get(
            spreadsheetId=spreadsheet_id, range=rng
        ).execute()
    except Exception as e:
        return jsonify({"error": f"Failed to re-read values: {str(e)}"}), 500
    a_values = result2.get("values", [])
    if not a_values:
        return jsonify({
            "message": "Task deleted (row removed). No remaining tasks to renumber.",
            "deleted_row": target_row_index_1based
        }), 200
    first = (a_values[0][0] or "").strip()
    def _safe_int_from_wbs(w):
        try:
            return int(w.lower().replace("wbs", "").strip())
        except Exception:
            return None
    start_num = _safe_int_from_wbs(first)
    if start_num is None:
        start_num = 0
    new_wbs_col = [[f"wbs{start_num + i}"] for i in range(len(a_values))]
    try:
        service.spreadsheets().values().update(
            spreadsheetId=spreadsheet_id,
            range=f"{sheet_title}!A2:A{len(new_wbs_col)+1}",
            valueInputOption="RAW",
            body={"values": new_wbs_col}
        ).execute()
    except Exception as e:
        return jsonify({"error": f"Renumber failed: {str(e)}"}), 500
    return jsonify({
        "message": "Task deleted (row removed) and WBS renumbered",
        "deleted_row": target_row_index_1based,
        "renumber": {"start": start_num, "count": len(new_wbs_col)}
    }), 200
# ========= Calendar Service Helper =========
def get_user_calendar_service(user_id: str):
    creds = load_user_credentials(user_id)
    if not creds:
        return None
    return build("calendar", "v3", credentials=creds, cache_discovery=False)
# ========= 日付/時刻ユーティリティ =========
def _parse_date_yyyy_mm_dd(s: str) -> Optional[datetime.date]:
    try:
        return datetime.strptime(s, "%Y-%m-%d").date()
    except Exception:
        return None
def _parse_hh_mm(s: str) -> Optional[datetime.time]:
    try:
        return datetime.strptime(s, "%H:%M").time()
    except Exception:
        return None
def start_of_week(d: datetime.date) -> datetime.date:
    # 月曜始まり（0=Mon）で週の開始日を返す
    return d - timedelta(days=d.weekday())
def next_monday(today: Optional[datetime.date] = None) -> datetime.date:
    today = today or datetime.utcnow().date()
    n = (7 - today.weekday()) % 7
    n = 1 if n == 0 else n  # きょうが月曜でも次週の月曜に飛ぶ
    return today + timedelta(days=n)
def rfc3339(dt_date: datetime.date, hhmm: Optional[str]) -> Optional[str]:
    # hhmm が無ければ None（＝終日扱い）
    if not hhmm:
        return None
    # "YYYY-MM-DDTHH:MM:00+09:00" 形式に整形
    return f"{dt_date.isoformat()}T{hhmm}:00{TZ_OFFSET}"
def make_event_id(user_id: str, wbs: str, date_str: str) -> str:
    raw = f"{user_id}|{wbs}|{date_str}".lower().encode()
    h = hashlib.sha1(raw).hexdigest()
    return f"gpts-{h}"  # [a-z0-9-] で 5〜1024 文字OK
@app.route("/preview_week", methods=["POST"])
def preview_week():
    """
    指定 week_of(YYYY-MM-DDのどこかの日) を含む週の予定を返す。
    無指定なら「次週の月〜日」を返す。
    返却は get_tasks と同じキー（WBS, Date, Start, End, Task Name, Status, Note）
    """
    
    # 置換
    data = request.get_json() or {}
    user_id = (data.get("user_id") or "").strip()
    week_of = (data.get("week_of") or "").strip()  # 例: "2025-08-18"（任意）
    if not user_id:
        return jsonify({"error": "user_id is required"}), 400
    # シート読込
    try:
        spreadsheet_id = get_user_spreadsheet_id(user_id)
    except ValueError:
        return jsonify({"error": "spreadsheet not found"}), 404
    service = get_user_sheets_service(user_id)
    if service is None:
        return jsonify({"error": "Authorization required"}), 401
    try:
        meta = service.spreadsheets().get(spreadsheetId=spreadsheet_id).execute()
        sheet_title = meta["sheets"][0]["properties"]["title"]
        res = service.spreadsheets().values().get(
            spreadsheetId=spreadsheet_id, range=f"{sheet_title}!A1:G10000"
        ).execute()
    except Exception as e:
        return jsonify({"error": f"Failed to read sheet: {str(e)}"}), 500
    values = res.get("values", [])
    if not values or len(values) < 2:
        return jsonify({"tasks": []})
    headers = values[0]
    rows = values[1:]
    # 週範囲決定
    if week_of:
        base = _parse_date_yyyy_mm_dd(week_of) or datetime.utcnow().date()
        monday = start_of_week(base)
    else:
        monday = next_monday()
    sunday = monday + timedelta(days=6)
    # フィルタ
    out = []
    for r in rows:
        row = {headers[i]: (r[i] if i < len(r) else "") for i in range(len(headers))}
        d = _parse_date_yyyy_mm_dd((row.get("Date") or "").strip())
        if not d:
            continue
        if monday <= d <= sunday:
            out.append(row)
    return jsonify({
        "week": {"start": monday.isoformat(), "end": sunday.isoformat()},
        "tasks": out
    })
@app.route("/calendar/register_week", methods=["POST"])
def calendar_register_week():
    """
    指定週のタスクを Google カレンダーに登録。
    body:
      {
        "user_id": "...",
        "week_of": "YYYY-MM-DD",    # 任意。未指定なら次週。
        "calendar_id": "primary",   # 任意。既定=primary
        "dry_run": false            # 任意。trueなら作成せず差分だけ返す
      }
    """
    data = request.get_json() or {}
    user_id = (data.get("user_id") or "").strip()
    week_of = (data.get("week_of") or "").strip()
    calendar_id = (data.get("calendar_id") or "primary").strip()
    dry_run = bool(data.get("dry_run", False))
    if not user_id:
        return jsonify({"error": "user_id is required"}), 400
    # まずプレビューを再利用
    resp = preview_week()
    prev = resp.get_json()  # ← ここが大事
    if isinstance(prev, dict) and "error" in prev:
        return jsonify(prev), 400

    tasks = prev.get("tasks", [])
    week = prev.get("week", {})
    if not tasks:
        return jsonify({"message": "No tasks in the target week", "week": week, "created": []})
    cal = get_user_calendar_service(user_id)
    if cal is None:
        # 再認可（Calendar scope 追加のため必要になる場合あり）
        flow = build_flow()
        auth_url, _ = flow.authorization_url(
            access_type="offline", include_granted_scopes="true", prompt="consent",
            state=signed_state(user_id)
        )
        return jsonify({
            "requires_auth": True,
            "authorize_url": auth_url,
            "message": "Calendar authorization required. Please authorize and retry."
        }), 200
    created, updated, skipped = [], [], []
    for row in tasks:
        wbs = (row.get("WBS") or "").strip()
        date_str = (row.get("Date") or "").strip()
        task_name = (row.get("Task Name") or "").strip() or (row.get("task") or "").strip()
        status = (row.get("Status") or "").strip()
        note = (row.get("Note") or "").strip()
        start_hhmm = (row.get("Start") or row.get("start") or "").strip()
        end_hhmm = (row.get("End") or row.get("end") or "").strip()
        duration_min = None
        try:
            duration_min = int((row.get("Duration") or "0").strip())
        except Exception:
            pass
        # 終日 or 時刻指定
        start_iso = rfc3339(_parse_date_yyyy_mm_dd(date_str), start_hhmm)
        if start_iso:
            if end_hhmm:
                end_iso = rfc3339(_parse_date_yyyy_mm_dd(date_str), end_hhmm)
            else:
                # End 未指定: Duration があればそれを使う、無ければ +60分
                hh, mm = map(int, start_hhmm.split(":"))
                mins = duration_min if duration_min and duration_min > 0 else 60
                end_dt = datetime.strptime(f"{date_str} {start_hhmm}", "%Y-%m-%d %H:%M") + timedelta(minutes=mins)
                end_iso = f"{end_dt.strftime('%Y-%m-%dT%H:%M')}:00{TZ_OFFSET}"
            body = {
                "summary": task_name or "学習タスク",
                "description": f"Status: {status}\nNote: {note}",
                "start": {"dateTime": start_iso, "timeZone": USER_TZ},
                "end": {"dateTime": end_iso, "timeZone": USER_TZ},
                "extendedProperties": {"private": {"gpts_wbs": wbs, "gpts_date": date_str}},
            }
        else:
            # 終日イベント
            body = {
                "summary": task_name or "学習タスク（終日）",
                "description": f"Status: {status}\nNote: {note}",
                "start": {"date": date_str},
                "end": {"date": (datetime.strptime(date_str, "%Y-%m-%d").date() + timedelta(days=1)).isoformat()},
                "extendedProperties": {"private": {"gpts_wbs": wbs, "gpts_date": date_str}},
            }
        ev_id = make_event_id(user_id, wbs or "no-wbs", date_str or "no-date")
        if dry_run:
            skipped.append({"id": ev_id, "title": body["summary"], "date": date_str})
            continue
        try:
            cal.events().insert(calendarId=calendar_id, body=body, sendUpdates="none", conferenceDataVersion=0, supportsAttachments=False, maxAttendees=1, sendNotifications=False, quotaUser=user_id, eventId=ev_id).execute()
            created.append({"id": ev_id, "title": body["summary"], "date": date_str})
        except Exception as e:
            msg = str(e)
            # 既存（409等）なら update に切替
            if "already exists" in msg or "Duplicate" in msg or "409" in msg:
                try:
                    cal.events().update(calendarId=calendar_id, eventId=ev_id, body=body, sendUpdates="none").execute()
                    updated.append({"id": ev_id, "title": body["summary"], "date": date_str})
                except Exception as e2:
                    skipped.append({"id": ev_id, "error": f"update failed: {e2}"})
            else:
                skipped.append({"id": ev_id, "error": msg})
    return jsonify({
        "week": week,
        "calendar_id": calendar_id,
        "created": created,
        "updated": updated,
        "skipped": skipped
    }), 200
@app.route("/calendar/register_by_wbs", methods=["POST"])
def calendar_register_by_wbs():
    """
    指定された WBS 行だけを登録/更新。
    body:
      {
        "user_id": "...",
        "wbs_ids": ["wbs12","wbs13"],
        "calendar_id": "primary",
        "dry_run": false
      }
    """
    data = request.get_json() or {}
    user_id = (data.get("user_id") or "").strip()
    wbs_ids = data.get("wbs_ids") or []
    calendar_id = (data.get("calendar_id") or "primary").strip()
    dry_run = bool(data.get("dry_run", False))
    if not user_id or not wbs_ids:
        return jsonify({"error": "user_id and wbs_ids are required"}), 400
    # シート読み出し
    try:
        spreadsheet_id = get_user_spreadsheet_id(user_id)
    except ValueError:
        return jsonify({"error": "spreadsheet not found"}), 404
    svc = get_user_sheets_service(user_id)
    if svc is None:
        return jsonify({"error": "Authorization required"}), 401
    try:
        meta = svc.spreadsheets().get(spreadsheetId=spreadsheet_id).execute()
        sheet_title = meta["sheets"][0]["properties"]["title"]
        res = svc.spreadsheets().values().get(
            spreadsheetId=spreadsheet_id, range=f"{sheet_title}!A1:G10000"
        ).execute()
    except Exception as e:
        return jsonify({"error": f"Failed to read sheet: {str(e)}"}), 500
    values = res.get("values", [])
    if not values or len(values) < 2:
        return jsonify({"error": "no tasks" }), 404
    headers = values[0]
    rows = values[1:]
    # 対象行の抽出
    target = []
    for r in rows:
        row = {headers[i]: (r[i] if i < len(r) else "") for i in range(len(headers))}
        if (row.get("WBS") or "").strip() in set(wbs_ids):
            target.append(row)
    if not target:
        return jsonify({"error": "specified WBS not found"}), 404
    cal = get_user_calendar_service(user_id)
    if cal is None:
        flow = build_flow()
        auth_url, _ = flow.authorization_url(
            access_type="offline", include_granted_scopes="true", prompt="consent",
            state=signed_state(user_id)
        )
        return jsonify({
            "requires_auth": True,
            "authorize_url": auth_url,
            "message": "Calendar authorization required. Please authorize and retry."
        }), 200
    created, updated, skipped = [], [], []
    for row in target:
        wbs = (row.get("WBS") or "").strip()
        date_str = (row.get("Date") or "").strip()
        task_name = (row.get("Task Name") or "").strip() or (row.get("task") or "").strip()
        status = (row.get("Status") or "").strip()
        note = (row.get("Note") or "").strip()
        start_hhmm = (row.get("Start") or row.get("start") or "").strip()
        end_hhmm = (row.get("End") or row.get("end") or "").strip()
        duration_min = None
        try:
            duration_min = int((row.get("Duration") or "0").strip())
        except Exception:
            pass
        start_iso = rfc3339(_parse_date_yyyy_mm_dd(date_str), start_hhmm)
        if start_iso:
            if end_hhmm:
                end_iso = rfc3339(_parse_date_yyyy_mm_dd(date_str), end_hhmm)
            else:
                hh, mm = map(int, start_hhmm.split(":"))
                mins = duration_min if duration_min and duration_min > 0 else 60
                end_dt = datetime.strptime(f"{date_str} {start_hhmm}", "%Y-%m-%d %H:%M") + timedelta(minutes=mins)
                end_iso = f"{end_dt.strftime('%Y-%m-%dT%H:%M')}:00{TZ_OFFSET}"
            body = {
                "summary": task_name or "学習タスク",
                "description": f"Status: {status}\nNote: {note}",
                "start": {"dateTime": start_iso, "timeZone": USER_TZ},
                "end": {"dateTime": end_iso, "timeZone": USER_TZ},
                "extendedProperties": {"private": {"gpts_wbs": wbs, "gpts_date": date_str}},
            }
        else:
            body = {
                "summary": task_name or "学習タスク（終日）",
                "description": f"Status: {status}\nNote: {note}",
                "start": {"date": date_str},
                "end": {"date": (datetime.strptime(date_str, "%Y-%m-%d").date() + timedelta(days=1)).isoformat()},
                "extendedProperties": {"private": {"gpts_wbs": wbs, "gpts_date": date_str}},
            }
        ev_id = make_event_id(user_id, wbs or "no-wbs", date_str or "no-date")
        if dry_run:
            skipped.append({"id": ev_id, "title": body["summary"], "date": date_str})
            continue
        try:
            cal.events().insert(calendarId=calendar_id, body=body, eventId=ev_id, sendUpdates="none").execute()
            created.append({"id": ev_id, "title": body["summary"], "date": date_str})
        except Exception as e:
            if "already exists" in str(e) or "Duplicate" in str(e) or "409" in str(e):
                try:
                    cal.events().update(calendarId=calendar_id, eventId=ev_id, body=body, sendUpdates="none").execute()
                    updated.append({"id": ev_id, "title": body["summary"], "date": date_str})
                except Exception as e2:
                    skipped.append({"id": ev_id, "error": f"update failed: {e2}"})
            else:
                skipped.append({"id": ev_id, "error": str(e)})
    return jsonify({
        "calendar_id": calendar_id,
        "created": created,
        "updated": updated,
        "skipped": skipped
    }), 200

# 例：末尾あたりに追加
@app.route("/check")
def check():
    return "main.py loaded, revision OK"

if __name__ == "__main__":
    port = int(os.environ.get("PORT", 8080))
    app.run(host="0.0.0.0", port=port)
