;----------------------------------------------------------------------
; Tac System Installer
;----------------------------------------------------------------------
!include "MUI2.nsh"
!include "LogicLib.nsh"
!include "VersionCompare.nsh"
!include "path.nsh"

; Grab the output from taci.  Assumes that perl is installed; would be better not to need it.
!system '..\bin\taci --version | perl -pe "s/Taci version/!define VERSION/" > version.nsh'
!include "version.nsh"

; Installer Name:
Name "Tac"

; The file to write
OutFile "Tac-${VERSION}.exe"

; The default installation directory
InstallDir "$PROGRAMFILES\Tac"

; Registry key to check for directory (so if you install again, it will 
; overwrite the old one automatically)
InstallDirRegKey HKLM "Software\Tac" "Install_Dir"

; Request application privileges for Windows Vista
RequestExecutionLevel admin

;----------------------------------------------------------------------
; Functions to verify that .NET is installed.
;----------------------------------------------------------------------
Function GetDotNETVersion
  Push $0
  Push $1
 
  System::Call "mscoree::GetCORVersion(w .r0, i ${NSIS_MAX_STRLEN}, *i) i .r1 ?u"
  StrCmp $1 "error" 0 +2
    StrCpy $0 "not found"
 
  Pop $1
  Exch $0
FunctionEnd

Function .onInit
  Call GetDotNETVersion
  Pop $0
  ${If} $0 == "not found"
    MessageBox MB_OK|MB_ICONSTOP "Tac requires the Microsoft .NET Framework version 2.0."
    Abort
  ${EndIf}
 
  StrCpy $0 $0 "" 1 # skip "v"
 
  ${VersionCompare} $0 "2.0" $1
  ${If} $1 == 2
    MessageBox MB_OK|MB_ICONSTOP "Tac requires the Microsoft .NET Framework version 2.0; version $0 is currently installed."
    Abort
  ${EndIf}
FunctionEnd

;----------------------------------------------------------------------
; Pages
;----------------------------------------------------------------------
!insertmacro MUI_PAGE_DIRECTORY
!insertmacro MUI_PAGE_INSTFILES
!define MUI_FINISHPAGE_TEXT "Tac has been installed successfully. The directory '$INSTDIR\bin' has been added to your path."
!insertmacro MUI_PAGE_FINISH

!insertmacro MUI_UNPAGE_CONFIRM
!insertmacro MUI_UNPAGE_INSTFILES

;----------------------------------------------------------------------
;Languages
;----------------------------------------------------------------------
!insertmacro MUI_LANGUAGE "English"

;----------------------------------------------------------------------
; Files to Install
;----------------------------------------------------------------------
Section "Tac (required)"
  ; Copy the binaries.
  SetOutPath $INSTDIR
  File /r /x .svn /x StickyTaci /x logics_gen /x *.pdb "..\bin"

  ; Copy the examples.
  SetOutPath $INSTDIR
  File /r /x .svn "..\examples"

  ; Copy the README files; we have more than 1.
  SetOutPath $INSTDIR
  File "..\README*"

  ; Add to user's $PATH
  Push $INSTDIR\bin
  Call AddToPath
    
  ; Write the installation path into the registry
  WriteRegStr HKLM SOFTWARE\Tac "Install_Dir" "$INSTDIR"
  
  ; Write the uninstall keys for Windows
  WriteRegStr HKLM "Software\Microsoft\Windows\CurrentVersion\Uninstall\Tac" "DisplayName" "Tac"
  WriteRegStr HKLM "Software\Microsoft\Windows\CurrentVersion\Uninstall\Tac" "UninstallString" '"$INSTDIR\uninstall.exe"'
  WriteRegDWORD HKLM "Software\Microsoft\Windows\CurrentVersion\Uninstall\Tac" "NoModify" 1
  WriteRegDWORD HKLM "Software\Microsoft\Windows\CurrentVersion\Uninstall\Tac" "NoRepair" 1
  WriteUninstaller "uninstall.exe"

  ; Create shortcuts
  CreateDirectory "$SMPROGRAMS\Tac"
  CreateShortCut "$SMPROGRAMS\Tac\StickyTaci.lnk" "$INSTDIR\bin\StickyTaci.exe"
  CreateShortCut "$SMPROGRAMS\Tac\Taci.lnk" "$INSTDIR\bin\Taci.exe"
  CreateShortCut "$SMPROGRAMS\Tac\Uninstall.lnk" "$INSTDIR\uninstall.exe"
SectionEnd

;----------------------------------------------------------------------
; Uninstaller
;----------------------------------------------------------------------
Section "Uninstall"
  
  ; Remove registry keys
  DeleteRegKey HKLM "Software\Microsoft\Windows\CurrentVersion\Uninstall\Tac"
  DeleteRegKey HKLM SOFTWARE\Tac

  ; Remove from user's $PATH
  Push $INSTDIR
  Call un.RemoveFromPath

  ; Remove directories used
  RMDir /r "$INSTDIR"

  ; Delete shortcuts:
  RMDir /r "$SMPROGRAMS\Tac"

SectionEnd
