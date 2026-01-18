# Coq + QuickChick + SMTCoq Docker Image for Verina
# Build: docker build -f docker/Dockerfile.coq -t verina-coq .
# Run: docker run --rm -v "$(pwd):/workspace" verina-coq coqc /workspace/file.v

FROM coqorg/coq:8.18

# Install veriT SMT solver (required for SMTCoq)
USER root
RUN apt-get update && apt-get install -y \
    wget \
    build-essential \
    libgmp-dev \
    flex \
    bison \
    autoconf \
    && rm -rf /var/lib/apt/lists/*

# Download and build veriT (SMTCoq-compatible snapshot)
# Source: https://usr.lmf.cnrs.fr/~ckeller/Documents-recherche/Smtcoq/
# Note: -fcommon is needed for GCC 10+ compatibility with old C code
RUN cd /tmp && \
    wget https://usr.lmf.cnrs.fr/~ckeller/Documents-recherche/Smtcoq/veriT9f48a98.tar.gz && \
    tar xzf veriT9f48a98.tar.gz && \
    cd veriT9f48a98 && \
    autoconf && \
    ./configure && \
    make CFLAGS="-fcommon -Wall -finline-limit=1000000 -Wno-unused-function -O3 -DNDEBUG -fomit-frame-pointer" && \
    cp veriT /usr/local/bin/ && \
    cd / && rm -rf /tmp/veriT*

USER coq

# Install QuickChick and SMTCoq (version 2.2+8.18 for Coq 8.18)
RUN opam update && \
    opam install -y coq-quickchick coq-smtcoq.2.2+8.18 && \
    opam clean -a -c -s --logs

# Set working directory
WORKDIR /workspace

# Default command
CMD ["bash"]
