#!/usr/bin/env bash

set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REBUILD=false

if [[ "${1:-}" == "--rebuild" ]]; then
  REBUILD=true
elif [[ $# -gt 0 ]]; then
  echo "Usage: $0 [--rebuild]"
  exit 1
fi

if ! command -v devcontainer >/dev/null 2>&1; then
  echo "Error: 'devcontainer' CLI not found."
  echo "Install it with: npm install -g @devcontainers/cli"
  exit 1
fi

echo "Starting devcontainer for: ${ROOT_DIR}"
if [[ "${REBUILD}" == "true" ]]; then
  devcontainer up --workspace-folder "${ROOT_DIR}" --remove-existing-container
else
  devcontainer up --workspace-folder "${ROOT_DIR}"
fi

devcontainer exec --workspace-folder "${ROOT_DIR}" env TERM=$TERM bash
