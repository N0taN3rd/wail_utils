@echo off
setlocal enabledelayedexpansion

set here=%~dp0
set pycachew=%here%\wail_scripts\__pycache__
set pycachep=%here%\pywb_scripts\__pycache__
set build=%here%build
set realDistPath=%here%realDist
set builtPath=%realDistPath%\pywb
set resources=%here%resources
set pyinDistPath=%here%dist
set specPath=%here%specs

for %%f in (%realDistPath%,%pyinDistPath%,%build%, %pycachew%,%pycachep%) do (
	if exist %%f (
		echo cleaning %%f
		rmdir /s /q %%f
	) else (
		echo not exist %%f
	)
)

for %%f in ("%specPath%\*") do (
	if not exist %pyinDistPath%\%%~nf  (
		start /wait pyinstaller %%f
	)
)

if not exist %realDistPath%  (
	mkdir %realDistPath%
)

if not exist %builtPath% (
	mkdir %builtPath%
)

start /wait robocopy /s %resources% %builtPath%
start /wait robocopy /s %pyinDistPath%\wayback %builtPath%
start /wait robocopy /s %pyinDistPath%\wb-manager %builtPath%
start /wait robocopy /s %pyinDistPath%\cdx-indexer %builtPath%
start /wait robocopy /s %pyinDistPath%\cdx-server %builtPath%
start /wait robocopy /s %pyinDistPath%\warcChecker %realDistPath%\warcChecker
start /wait robocopy /s %pyinDistPath%\listUris %realDistPath%\listUris

for %%f in (%build%, %pyinDistPath%, %pycachew%,%pycachep%) do (
	if exist %%f (
		echo cleaning %%f
		rmdir /s /q %%f
	) else (
		echo not exist %%f
	)
)
