FROM node:24-alpine AS frontend

WORKDIR /app
COPY frontend/package.json frontend/package-lock.json ./
RUN npm ci
COPY frontend/ ./
RUN npm run build

FROM nginx:1.28-alpine

RUN apk add --no-cache openssl
COPY deploy/nginx/templates/ /etc/nginx/templates/
COPY deploy/nginx/frontend.static.conf /etc/nginx/cloverleaf/frontend.conf
COPY --chmod=755 deploy/nginx/generate-cert.sh /docker-entrypoint.d/10-generate-cert.sh
COPY --from=frontend /app/dist /usr/share/nginx/html
