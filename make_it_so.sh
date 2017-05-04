#!/usr/bin/env bash


here=$(pwd)
realDistPath="$here/realDist"
builtPath="$realDistPath/pywb"
resources="$here/resources"
pyinDistPath="$here/dist"
specPath="$here/specs"
tarPath="$here/$BUILDFOR.tar.gz"
distToTar="$here/realDist/*"

clean () {
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


fclean () {
  if [[ -d "pywb" ]]; then
     echo cleaning old build
     rm -rf pywb
  fi
  if [[ -d "realDist" ]]; then
     echo cleaning old realDist
     rm -rf realDist
  fi
  clean
}


build () {
  for installSpec in `ls ${specPath}/*.spec`
  do
    echo ${installSpec}
    pyinstaller ${installSpec}
  done
  mkdir ${realDistPath}
  mkdir ${builtPath}
  cp -r ${resources}/* ${builtPath}
  cp -r ${pyinDistPath}/wayback/* ${builtPath}
  cp  ${pyinDistPath}/cdx-indexer/cdx-indexer ${builtPath}
  cp  ${pyinDistPath}/wb-manager/wb-manager ${builtPath}
  cp -r ${pyinDistPath}/warcChecker ${realDistPath}
  cp -r ${pyinDistPath}/listUris ${realDistPath}
  tar -cvf ${tarPath} ${distToTar}
}

fclean
build
clean

