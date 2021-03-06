# -*- mode: python -*-
import os, os.path


here = os.getcwd()
name='wayback'
scriptPath = os.path.join(here,'pywb_scripts','%s.py'%name)
block_cipher = None

added_files = [
  ('%s/resources/*.yaml'%here, '.'),
  ('%s/resources/uwsgi.ini'%here,'.'),
  ('%s/resources/pywb'%here,'pywb')
]

a = Analysis([scriptPath],
             pathex=[here],
             binaries=[],
             datas=[],
             hiddenimports=[],
             hookspath=[],
             runtime_hooks=[],
             excludes=[],
             win_no_prefer_redirects=False,
             win_private_assemblies=False,
             cipher=block_cipher)
pyz = PYZ(a.pure, a.zipped_data,
             cipher=block_cipher)
exe = EXE(pyz,
          a.scripts,
          exclude_binaries=True,
          name=name,
          debug=False,
          strip=False,
          upx=True,
          console=True )
coll = COLLECT(exe,
               a.binaries,
               a.zipfiles,
               a.datas,
               strip=False,
               upx=True,
               name=name)
