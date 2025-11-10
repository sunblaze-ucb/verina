#!/bin/bash

# Update lean-toolchain file
sed -i 's/v4\.18\.0/v4.24.0/g' lean-toolchain

# Update lakefile.lean file
sed -i 's/v4\.18\.0/v4.24.0/g' lakefile.lean

echo "Updated Lean version from v4.18.0 to v4.24.0 in lean-toolchain and lakefile.lean"

echo "Running lake update..."

lake update
