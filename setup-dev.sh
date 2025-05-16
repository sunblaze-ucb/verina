#!/bin/bash

# Sync dependencies
echo "Syncing dependencies ..."
uv sync

# Install pre-commit hooks
echo "Installing pre-commit hooks ..."
if [ -f ".pre-commit-config.yaml" ]; then
    pre-commit install
else
    echo "No pre-commit configuration file found. Skipping pre-commit installation."
fi
