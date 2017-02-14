#!/usr/bin/env bash

here=$(pwd)
distDir="$here/dist"
pywbDist="$distDir/pywb"

cleanPywb () {
  if [[ -d "pywb/build" ]]; then
    echo cleaning build
    rm -rf pywb/build
  fi

  if [[ -d "pywb/dist"  ]]; then
    echo cleaning dist
    rm -rf pywb/dist
  fi

  if [[ -d "pywb/__pycache__"  ]]; then
    echo cleaning pycache
    rm -rf pywb/__pycache__
  fi
}

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
  cleanPywb
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
  cleanPywb
}

buildPywb () {
  mkdir -p dist/pywb
  cd pywb
  for fname in `ls *.spec`
  do
      base=$(basename "$fname")
      echo "$base"
      pyinstaller $base
      filename="${base%.*}"
      echo ${filename}

      if [[ "$filename" == "wayback" ]]; then
          chmod a+x "dist/pywb/wayback"
          cp -RT dist/pywb ${pywbDist}
      else
          chmod a+x "dist/$filename/$filename"
          cp "dist/$filename/$filename" ${pywbDist}
      fi
  done
  mkdir ${pywbDist}/pywb
  cp -r ${pywbDist}/static ${pywbDist}/pywb
  cp -r ${pywbDist}/templates ${pywbDist}/pywb
}



fclean

pyinstaller listUris.py
pyinstaller warcChecker.py
buildPywb

clean

