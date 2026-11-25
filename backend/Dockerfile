# Builds from the repo root, for the backend's three images:
#
#   docker build -f backend/Dockerfile --target road .   # road process and data
#   docker build -f backend/Dockerfile --target solver . # solver process
#   docker build -f backend/Dockerfile --target web .    # web process
#
# The road image carries every state's road data. By default the build fetches
# the US extract and rebuilds the data from scratch, which is what a deployed
# image ships. ROAD_DATA=local copies the cached data/road instead, which is
# what local Compose runs use. scripts/road-build.mjs defines the data format.
ARG ROAD_DATA=fresh

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
COPY backend/ .
RUN bend PROOF.bend \
  && bend web/main.bend --check-only \
  && bend road/main.bend --check-only \
  && bend solver/main.bend --check-only \
  && bend web/spec.bend > /tmp/openapi.json \
  && cmp /tmp/openapi.json openapi.json \
  && mkdir -p /out \
  && bend test/scenario.bend -o /out/scenario \
  && /out/scenario \
  && bend web/main.bend -o /out/web \
  && bend road/main.bend -o /out/road \
  && bend solver/main.bend -o /out/solver

# Road data rebuilt from OpenStreetMap. The 12GB download is deleted in the same
# step, so only the result reaches a layer.
FROM node:24-alpine AS road-data-fresh
WORKDIR /app
COPY scripts/fetch-road-data.mjs scripts/road-build.mjs scripts/road-turns.mjs scripts/check-road-data.mjs scripts/rebuild-road-data.mjs scripts/OSRM-LICENSE.txt ./
RUN node rebuild-road-data.mjs /data && rm -rf /data/osm

# The road data already built in data/road.
FROM scratch AS road-data-local
COPY data/road /data/road

FROM road-data-${ROAD_DATA} AS road-data

FROM ubuntu:24.04 AS runtime
RUN useradd --system --no-create-home cloverleaf

# Batch lookups against /road/<state>. Jobs read and write files in /jobs.
FROM runtime AS road
COPY --from=build /out/road /usr/local/bin/road
COPY --from=road-data /data/road /road
USER cloverleaf
WORKDIR /jobs
ENTRYPOINT ["road", "+RTS", "--threads", "6", "-RTS"]

# The nightly solve, one run per night. It reads each state's instance.bin and
# matrix.bin from /jobs and writes each plan beside them.
FROM runtime AS solver
COPY --from=build /out/solver /usr/local/bin/solver
USER cloverleaf
WORKDIR /jobs
ENTRYPOINT ["solver", "+RTS", "--threads", "6", "-RTS"]

FROM runtime AS web
COPY --from=build /out/web /usr/local/bin/web
USER cloverleaf
EXPOSE 8080
CMD ["web", "+RTS", "--threads", "2", "-RTS"]
