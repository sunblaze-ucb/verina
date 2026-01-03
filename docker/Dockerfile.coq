# Coq + QuickChick Docker Image for Verina
# Build: docker build -f docker/Dockerfile.coq -t verina-coq .
# Run: docker run --rm -v "$(pwd):/workspace" verina-coq coqc /workspace/file.v

FROM coqorg/coq:8.18

# Install QuickChick and other useful libraries
RUN opam update && \
    opam install -y coq-quickchick && \
    opam clean -a -c -s --logs

# Set working directory
WORKDIR /workspace

# Default command
CMD ["bash"]
