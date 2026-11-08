# The road build runs before deploy, on Node alone. It has its own image so that
# the Bend images stay free of Node.
FROM node:24-alpine

WORKDIR /app
COPY fetch-road-data.mjs road-build.mjs road-turns.mjs check-road-data.mjs rebuild-road-data.mjs OSRM-LICENSE.txt ./
USER node
CMD ["node", "rebuild-road-data.mjs", "/data"]
