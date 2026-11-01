#!/bin/sh
# Creates a self-signed certificate on first start. It lives in a Docker volume
# and is never committed.
set -eu

dir=/etc/nginx/certs
if [ -f "$dir/tls.crt" ] && [ -f "$dir/tls.key" ]; then
  exit 0
fi

openssl req -x509 -newkey rsa:2048 -nodes -days 825 \
  -subj "/CN=localhost" \
  -addext "subjectAltName=DNS:localhost,IP:127.0.0.1" \
  -keyout "$dir/tls.key" -out "$dir/tls.crt"
chmod 600 "$dir/tls.key"
