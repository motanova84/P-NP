# ==========================================
# Φ-LOCK v1.0 — Multi-Stage Docker Build
# Stage 1: Compile with protobuf
# ==========================================
FROM rust:1.78-alpine AS builder

RUN apk add --no-cache build-base protobuf-dev musl-dev

WORKDIR /usr/src/phi-lock

COPY Cargo.toml Cargo.lock ./
COPY proto ./proto
COPY build.rs ./

RUN mkdir src && \
    echo "fn main() {}" > src/main.rs && \
    cargo build --release 2>/dev/null; \
    rm -rf src

COPY src ./src
RUN touch src/main.rs && cargo build --release

# ==========================================
# Stage 2: Ultra-light runtime image
# ==========================================
FROM alpine:3.19

RUN apk add --no-cache ca-certificates libgcc

WORKDIR /app

COPY --from=builder /usr/src/phi-lock/target/release/phi-lock-p2p /app/phi-lock-p2p
RUN mkdir -p /app/config
COPY config/nodes.json /app/config/nodes.json

EXPOSE 50051 8080

ENV NODE_ID=1
ENV CONFIG_PATH=/app/config/nodes.json

CMD ["sh", "-c", "/app/phi-lock-p2p --node-id ${NODE_ID} --config ${CONFIG_PATH}"]
