FROM ubuntu:noble-20251001

RUN --mount=type=cache,target=/var/cache/apt,sharing=locked \
    --mount=type=cache,target=/var/lib/apt,sharing=locked \
    apt-get update \
    && apt-get install -y --no-install-recommends build-essential cmake libreadline-dev libmpfr-dev zlib1g-dev libsoplex-dev soplex python3 curl ca-certificates

RUN \
    mkdir /tmp/scip \
    && cd /tmp/scip \
    && curl -L https://github.com/scipopt/scip/archive/b9cbe65ddcc59436e729cc3cf3c1cbb67567c79f.tar.gz | tar zx --strip-components=1 \
    && mkdir build \
    && cd build \
    && cmake .. -DCMAKE_INSTALL_PREFIX=/usr/local -DAUTOBUILD=ON \
    && make \
    && make install \
    && cd ../.. \
    && rm -r scip
