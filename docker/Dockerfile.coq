# Coq + QuickChick + CoqHammer Docker Image for Verina
# Build: docker build -f docker/Dockerfile.coq -t verina-coq .
# Run: docker run --rm -v "$(pwd):/workspace" verina-coq coqc /workspace/file.v

FROM coqorg/coq:8.18

# Install ATP provers for CoqHammer's hammer tactic
USER root
RUN apt-get update && apt-get install -y \
    wget unzip eprover z3 cvc4 \
    && rm -rf /var/lib/apt/lists/*

# Download Vampire binary (not in apt)
RUN cd /tmp && \
    wget https://github.com/vprover/vampire/releases/download/v5.0.1/vampire-Linux-X64.zip && \
    unzip vampire-Linux-X64.zip && \
    cp vampire /usr/local/bin/ && \
    chmod +x /usr/local/bin/vampire && \
    rm -rf /tmp/vampire*

USER coq

# Install QuickChick, CoqHammer, and z3_tptp (Z3 TPTP frontend for hammer)
RUN opam update && \
    opam install -y coq-quickchick coq-hammer.1.3.2+8.18 z3_tptp && \
    opam clean -a -c -s --logs

# Set opam environment variables for non-interactive shells
ENV OPAM_SWITCH_PREFIX="/home/coq/.opam/default"
ENV CAML_LD_LIBRARY_PATH="/home/coq/.opam/default/lib/stublibs:/home/coq/.opam/default/lib/ocaml/stublibs:/home/coq/.opam/default/lib/ocaml"
ENV OCAML_TOPLEVEL_PATH="/home/coq/.opam/default/lib/toplevel"
ENV PATH="/home/coq/.opam/default/bin:${PATH}"

# Set working directory
WORKDIR /workspace

# Default command
CMD ["bash"]
