/*
 *_____________________________________________________________________________
 *
 *                       File Association
 *_____________________________________________________________________________
 *
 * Based on code taken from http://nsis.sourceforge.net/File_Association
 *
 * Usage in script:
 * 1. !include "FileAssociation.nsh"
 * 2. [Section|Function]
 *      ${FileAssociationFunction} "Param1" "Param2" "..." $var
 *    [SectionEnd|FunctionEnd]
 *
 * FileAssociationFunction=[RegisterExtension|UnRegisterExtension]
 *
 *_____________________________________________________________________________
 *
 * ${RegisterExtension}
 *   "extension" "fileclass" "description" "program" "icon_id" "program_name"
 *
 * ${UnRegisterExtension}
 *   "extension" "fileclass"
 *
 */


!ifndef FileAssociation_INCLUDED
!define FileAssociation_INCLUDED

!include Util.nsh


!macro RegisterExtensionCall _EXTENSION _FILECLASS _DESCRIPTION _PROGRAM _ICON_ID _PROGRAM_NAME
  Push "${_PROGRAM_NAME}"
  Push "${_ICON_ID}"
  Push "${_PROGRAM}"
  Push "${_DESCRIPTION}"
  Push "${_FILECLASS}"
  Push "${_EXTENSION}"
  ${CallArtificialFunction} RegisterExtension_
!macroend

!macro UnRegisterExtensionCall _EXTENSION _FILECLASS
  Push "${_FILECLASS}"
  Push "${_EXTENSION}"
  ${CallArtificialFunction} UnRegisterExtension_
!macroend



!define RegisterExtension `!insertmacro RegisterExtensionCall`
!define un.RegisterExtension `!insertmacro RegisterExtensionCall`

!macro RegisterExtension
!macroend

!macro un.RegisterExtension
!macroend

!macro RegisterExtension_
  Exch $R0 ; extension
  Exch 1
  Exch $R1 ; fileclass
  Exch 2
  Exch $R2 ; description
  Exch 3
  Exch $R3 ; program
  Exch 4
  Exch $R4 ; icon_id
  Exch 5
  Exch $R5 ; program_name
  Push $0

  ReadRegStr $0 HKCR    "$R0"   "" ; get old fileclass
  StrCmp "$0" "" RegisterExtension_NoBackup  ; empty
  StrCmp "$0" "$R1" RegisterExtension_NoBackup  ; already our own
  WriteRegStr   HKCR    "$R0"   "$R1_backup"    "$0" ; backup old fileclass
RegisterExtension_NoBackup:
  WriteRegStr   HKCR    "$R0"   ""              "$R1" ; set new fileclass

  ReadRegStr $0 HKCR    "$R1"   "" ; get old fileclass details
  StrCmp "$0" "" 0 RegisterExtension_Skip
  WriteRegStr   HKCR    "$R1"   ""      "$R2" ; set description
  WriteRegStr   HKCR    "$R1\shell" ""  "open" ; set default action
  WriteRegStr   HKCR    "$R1\DefaultIcon" ""    "$R3,$R4" ; set file icon
RegisterExtension_Skip:
  WriteRegStr   HKCR    "$R1\shell\open" ""     "Run in $R5"
  WriteRegStr   HKCR    "$R1\shell\open\command" "" '"$R3" "%1"'
  WriteRegStr   HKCR    "$R1\shell\test" ""     "Test with $R5"
  WriteRegStr   HKCR    "$R1\shell\test\command" "" '"$R3" -t "%1"'

  Pop $0
  Pop $R5
  Pop $R0
  Pop $R1
  Pop $R2
  Pop $R3
  Pop $R4
!macroend



!define UnRegisterExtension `!insertmacro UnRegisterExtensionCall`
!define un.UnRegisterExtension `!insertmacro UnRegisterExtensionCall`

!macro UnRegisterExtension
!macroend

!macro un.UnRegisterExtension
!macroend

!macro UnRegisterExtension_
  Exch $R0 ; extension
  Exch 1
  Exch $R1 ; fileclass
  Push $0

  ReadRegStr $0 HKCR    "$R0"   "" ; get current fileclass
  StrCmp "$0" "$R1" 0 UnRegisterExtension_NotOurOwn ; only if we own it
  ReadRegStr $0 HKCR    "$R0"   "$R1_backup" ; get backup
  StrCmp "$0" "" 0 UnRegisterExtension_Restore ; if backup="" then delete
  DeleteRegKey  HKCR    "$R0"
  DeleteRegKey  HKCR    "$R1" ; delete fileclass details
  Goto UnRegisterExtension_NotOurOwn
UnRegisterExtension_Restore:
  WriteRegStr   HKCR    "$R0"   ""              $0 ; reset old fileclass
  DeleteRegValue HKCR   "$R0"   "$R1_backup"
  DeleteRegKey  HKCR    "$R1" ; delete fileclass details
UnRegisterExtension_NotOurOwn:

  Pop $0
  Pop $R1
  Pop $R0
!macroend

!endif # !FileAssociation_INCLUDED
