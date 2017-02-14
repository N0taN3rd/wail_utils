# -*- mode: python -*-

block_cipher = None

import os, os.path

here = os.path.abspath(os.path.join(os.getcwd(), os.pardir))
print(here)

added_files = [
  ('%s/pywb/*.yaml'%here, '.'),
  ('%s/static/'%here,'static'),
  ('%s/templates/'%here,'templates'),
  ('%s/pywb/uwsgi.ini'%here,'.')
]


a = Analysis(['cdxindexer.py'],
             pathex=['%s/pywb'%here],
             binaries=None,
             datas=added_files,
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
          name='cdxindexer',
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
               name='cdxindexer')
