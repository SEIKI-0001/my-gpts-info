# syntax=docker/dockerfile:1
FROM python:3.11-slim

WORKDIR /app
COPY requirements.txt .
RUN pip install --no-cache-dir -r requirements.txt

COPY . .
ENV PORT=8080
CMD exec gunicorn main:app -b 0.0.0.0:${PORT} --workers 2 --threads 8 --timeout 120
