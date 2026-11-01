# Bend releases are x64 or arm64. This digest pins the linux-x64 build.
FROM ubuntu:24.04 AS build

ARG BEND_VERSION=2.0.39
ARG BEND_SHA256=6cf462fd8f70b094a4950ebb709a9c4ffd8f1d1189d9cedf1fd63cd5d041c7ab

RUN apt-get update \
  && apt-get install -y --no-install-recommends ca-certificates clang curl libc6-dev \
  && curl -fsSL -o /tmp/bend.tar.gz \
    "https://github.com/bendlang/bend/releases/download/v${BEND_VERSION}/bend-${BEND_VERSION}-linux-x64.tar.gz" \
  && echo "${BEND_SHA256}  /tmp/bend.tar.gz" | sha256sum -c - \
  && tar xzf /tmp/bend.tar.gz -C /opt 2>/dev/null \
  && rm /tmp/bend.tar.gz

ENV PATH="/opt/bend/bin:${PATH}" BEND_HOME=/opt/bend BEND_NO_TELEMETRY=1

WORKDIR /src
COPY . .
RUN bend web/main.bend --check-only && mkdir -p /out && bend web/main.bend -o /out/web

FROM ubuntu:24.04

RUN useradd --system --no-create-home cloverleaf
COPY --from=build /out/web /usr/local/bin/web
USER cloverleaf
EXPOSE 8080
CMD ["web", "+RTS", "--threads", "2", "-RTS"]
