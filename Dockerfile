# Base image with opam + OCaml
FROM ocaml/opam:debian-12-ocaml-5.4

# Use bash so we can easily activate opam
SHELL ["/bin/bash", "-c"]

# Install system dependencies
RUN sudo apt-get update && \
    sudo apt-get install -y pkg-config libgmp-dev

# Install Rocq
RUN opam update && opam install -y coq.9.1.1

# Set working directory
WORKDIR /home/opam/semantic-separation

# Copy the repository
COPY --chown=opam:opam . .

# Fix permissions.
USER root
RUN chown -R opam:opam /home/opam/semantic-separation

# Build the project
RUN eval $(opam env) && \
    make -j$(nproc)

# Default shell when container runs
CMD ["/bin/bash"]
