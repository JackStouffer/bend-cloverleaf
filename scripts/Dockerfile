# The road build runs before deploy, on Node alone. It has its own image so that
# the Bend images stay free of Node.
FROM node:24-alpine

WORKDIR /app
COPY fetch-road-data.mjs road-build.mjs check-road-data.mjs ./
USER node
CMD ["sh", "-c", "node fetch-road-data.mjs /data/osm && node road-build.mjs /data/osm/us-latest.osm.pbf /data/osm/outlines /data/road && node check-road-data.mjs /data/road"]
