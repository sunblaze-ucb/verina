#!/bin/bash
# Setup script for Coq/Rocq development environment
# This script installs Coq and required packages via opam

set -e

echo "=== Verina Coq Setup Script ==="
echo ""

# Check if opam is installed
if ! command -v opam &> /dev/null; then
    echo "opam not found. Installing opam..."
    bash -c "sh <(curl -fsSL https://raw.githubusercontent.com/ocaml/opam/master/shell/install.sh)"
fi

# Initialize opam if not already done
if [ ! -d "$HOME/.opam" ]; then
    echo "Initializing opam..."
    opam init --bare -y
fi

# Check if verina-coq switch exists
if opam switch list 2>/dev/null | grep -q "verina-coq"; then
    echo "Switch 'verina-coq' already exists. Using existing switch."
    opam switch verina-coq
else
    echo "Creating opam switch 'verina-coq' with OCaml 4.14.1..."
    opam switch create verina-coq 4.14.1
fi

# Set up environment
eval $(opam env --switch=verina-coq)

# Add Coq repository
echo "Adding Coq opam repository..."
opam repo add coq-released https://coq.inria.fr/opam/released --set-default || true

# Update repository
echo "Updating opam repositories..."
opam update

# Install Coq/Rocq
echo "Installing Coq/Rocq..."
opam install rocq-core -y || opam install coq -y

# Install QuickChick for property-based testing
echo "Installing QuickChick..."
opam install coq-quickchick -y

# Install additional useful libraries
echo "Installing additional Coq libraries..."
opam install coq-mathcomp-ssreflect -y || echo "Warning: coq-mathcomp-ssreflect installation failed (optional)"

# Verify installation
echo ""
echo "=== Verifying installation ==="
echo "Coq version:"
coqc --version || echo "Warning: coqc not found in PATH"

echo ""
echo "=== Setup complete! ==="
echo ""
echo "To use Coq, run: eval \$(opam env --switch=verina-coq)"
echo "Or add this to your shell profile for automatic activation."
echo ""
echo "To test Coq compilation, run:"
echo "  cd $(dirname $0)/.."
echo "  python -c \"from verina.coq import check_coq_compile, create_coq_file; f = create_coq_file('test', 'Lemma test : 1 = 1. Proof. reflexivity. Qed.'); print(check_coq_compile(f))\""
