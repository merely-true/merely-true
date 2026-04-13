#!/usr/bin/env bash
# No-op: this project does not use the Mathlib Python style linters.
# Mathlib's `lint-style` binary invokes this script to run Python-based
# linters; here we exit successfully with no output so the `lint-style`
# action succeeds.
exit 0
