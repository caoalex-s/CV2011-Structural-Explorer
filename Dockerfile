FROM node:24-slim AS frontend
WORKDIR /source
COPY package.json ./
RUN npm install --ignore-scripts
COPY scripts/build.mjs ./scripts/build.mjs
COPY web ./web
RUN node scripts/build.mjs
FROM python:3.12-slim
WORKDIR /app
COPY requirements.txt ./
RUN pip install --no-cache-dir -r requirements.txt
COPY server ./server
COPY proofs ./proofs
COPY --from=frontend /source/dist ./dist
ENV EXPLORER_DATA=/data
EXPOSE 8765
CMD ["python", "-m", "server.app", "--host", "0.0.0.0"]
