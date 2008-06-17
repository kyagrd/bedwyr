;----------------------------------------------------------------------
; Tac System Installer
;----------------------------------------------------------------------
!include "MUI2.nsh"
!include "path.nsh"

; Grab the output from taci.  Assumes that perl is installed; would be better not to need it.
!system '..\bin\taci --version | perl -pe "s/Taci version/!define VERSION/" > version.nsh'
!include version.nsh

; Installer Name:
Name "Tac"

; The file to write
OutFile "Tac-${VERSION}.exe"

; The default installation directory
InstallDir $PROGRAMFILES\Tac

; Registry key to check for directory (so if you install again, it will 
; overwrite the old one automatically)
InstallDirRegKey HKLM "Software\Tac" "Install_Dir"

; Request application privileges for Windows Vista
RequestExecutionLevel admin

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
