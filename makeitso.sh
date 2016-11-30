#!/usr/bin/env bash

here=$(pwd)

fclean () {
  if [[ -d "build" ]]; then
    echo cleaning build
    rm -rf build
  fi

  if [[ -d "dist"  ]]; then
    echo cleaning dist
    rm -rf dist
  fi

  if [[ -d "__pycache__"  ]]; then
    echo cleaning pycache
    rm -rf __pycache__
  fi
}

clean () {
  if [[ -d "build" ]]; then
    echo cleaning build
    rm -rf build
  fi

  if [[ -d "__pycache__"  ]]; then
    echo cleaning pycache
    rm -rf __pycache__
  fi
}


fclean

pyinstaller listUris.py
pyinstaller warcChecker.py

clean

