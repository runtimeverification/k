#!/usr/bin/env bash
set -euo pipefail

# Kup relies on cachix registry k-framework-binary.
CACHE="k-framework-binary"
OWNER_REPO="${OWNER_REPO:-$(git remote get-url origin | sed -E 's#(git@github.com:|https://github.com/)##; s#\.git$##')}"
REV="${REV:-${GITHUB_SHA:-$(git rev-parse HEAD)}}"
UNAME_S="$(uname -s)"
UNAME_M="$(uname -m)"
case "${UNAME_S}-${UNAME_M}" in
  Linux-x86_64) SYSTEM="x86_64-linux" ;;
  Linux-aarch64 | Linux-arm64) SYSTEM="aarch64-linux" ;;
  Darwin-x86_64) SYSTEM="x86_64-darwin" ;;
  Darwin-arm64) SYSTEM="aarch64-darwin" ;;
  *)
    echo "Unsupported platform: ${UNAME_S}-${UNAME_M}" >&2
    exit 1
    ;;
esac
PIN_API_URL="https://app.cachix.org/api/v1/cache/${CACHE}/pin"
# Must match every attribute passed to `kup publish … .#…` for this cache.
CHECK_PACKAGES=(k k.openssl.secp256k1 k.openssl.procps.secp256k1)

SUMMARY="${GITHUB_STEP_SUMMARY:-/dev/stdout}"

{
  echo "## Cachix publish pin check"
  echo "CACHE: $CACHE"
  echo "OWNER_REPO: $OWNER_REPO"
  echo "REV: $REV"
  echo "SYSTEM: $SYSTEM"
  echo "PACKAGES: ${CHECK_PACKAGES[*]}"
} >> "$SUMMARY"

PIN_VISIBILITY_TIMEOUT_SECONDS=120
PIN_VISIBILITY_INTERVAL_SECONDS=5
PIN_VISIBILITY_ATTEMPTS=$((PIN_VISIBILITY_TIMEOUT_SECONDS / PIN_VISIBILITY_INTERVAL_SECONDS))
for i in $(seq 1 "$PIN_VISIBILITY_ATTEMPTS"); do
  PIN_JSON="$(curl -fsSL "${PIN_API_URL}?q=${REV}")"
  ALL_OK=1

  for PKG in "${CHECK_PACKAGES[@]}"; do
    KEY="github:${OWNER_REPO}/${REV}#packages.${SYSTEM}.${PKG}"
    STORE_PATH="$(
      echo "$PIN_JSON" \
        | jq -r --arg k "$KEY" 'map(select(.name == $k)) | first | (.lastRevision.storePath // .storePath // .store_path // .path // "")'
    )"
    if [ -z "$STORE_PATH" ]; then
      PIN_STATUS="pin-missing"
      PUSH_STATUS="000"
      ALL_OK=0
      {
        echo "key-${PKG}: ${KEY}"
        echo "pin-status-${PKG}: ${PIN_STATUS}"
        echo "push-http-${PKG}: ${PUSH_STATUS}"
      }
      continue
    fi

    PIN_STATUS="pin-ok"
    HASH="$(basename "$STORE_PATH" | cut -d- -f1)"
    PUSH_NARINFO_URL="https://${CACHE}.cachix.org/${HASH}.narinfo"
    PUSH_STATUS="$(curl -sS -o /dev/null -w '%{http_code}' "$PUSH_NARINFO_URL")" || PUSH_STATUS="000"
    if [ "$PUSH_STATUS" != "200" ]; then
      ALL_OK=0
    fi

    {
      echo "key-${PKG}: ${KEY}"
      echo "store-path-${PKG}: ${STORE_PATH}"
      echo "pin-status-${PKG}: ${PIN_STATUS}"
      echo "push-http-${PKG}: ${PUSH_STATUS}"
    }
  done

  if [ "$ALL_OK" = "1" ]; then
    echo "cachix-status: push-and-pin-ok-for-all-packages" >> "$SUMMARY"
    exit 0
  fi

  echo "cachix-check-attempt-${i}: not-ready, retrying in ${PIN_VISIBILITY_INTERVAL_SECONDS}s"
  sleep "$PIN_VISIBILITY_INTERVAL_SECONDS"
done

echo "cachix-status: push-or-pin-missing-after-${PIN_VISIBILITY_TIMEOUT_SECONDS}s-for-at-least-one-package" >> "$SUMMARY"
exit 1
