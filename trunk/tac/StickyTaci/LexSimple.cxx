// Scintilla source code edit control
/** @file LexSimple.cxx
 ** Lexer for any simple langage; there are relatively few assumptions placed on the kinds of
 ** characters that might be used as identifiers, and there are only 3 operators.  However, there
 ** is the hack of 'currentline'; any line before currentline is treated as 'old', and styled
 ** as such.  This is to support the hilighting found in StickyTaci, part of the Tac system.
 ** It supports multiline strings using ' or ", line comments using %, and that's about it.
 **/
// Copyright 2008 by Zach Snow.  Note that this was adapted from LexPython.cxx, which can
// be found in the Scintilla sources.
// The License.txt file describes the conditions under which this software may be distributed.
// Scintilla source code edit control.

//Rebuilding Scintilla with LexSimple.cxx
//  To get this working with Scintilla, first copy LexSimple.cxx into the src directory
//  of you're Scintiall install.  Then you'll need to add the following to the interface.
//  It should be easy to see where, just look at the code for python (SCE_PYTHON):
//    SCE_SIMPLE
//    SCE_SIMPLE_DEFAULT
//    SCE_SIMPLE_STRING
//    SCE_SIMPLE_NUMBER
//    SCE_SIMPLE_OPERATOR
//    SCE_SIMPLE_IDENTIFIER
//    SCE_SIMPLE_COMMENTLINE
//    SCE_SIMPLE_OLDLINE
//  Then, you'll need to regenerate the interface, regenerate the list of lexers (both are as
//  simple as running the correct python script), and recompile Scintilla.  And that's it.

#include <stdlib.h>
#include <string.h>
#include <ctype.h>
#include <stdio.h>
#include <stdarg.h>

#include "Platform.h"

#include "PropSet.h"
#include "Accessor.h"
#include "StyleContext.h"
#include "KeyWords.h"
#include "Scintilla.h"
#include "SciLexer.h"

#ifdef SCI_NAMESPACE
using namespace Scintilla;
#endif

static const int indicatorWhitespace = 1;

static bool IsOperator(int ch)
{
  return (ch < 0x80) &&
      (ch == '(' ||
      ch == ')' ||
      ch == ',');
}

static bool IsComment(Accessor &styler, int pos, int len) {
	return len > 0 && styler[pos] == '%';
}

static bool IsStringStart(int ch) {
	if (ch == '\'' || ch == '"')
		return true;
	return false;
}

static bool IsDigit(int ch)
{
  return (ch < 0x80) && (ch >= '0') && (ch <= '9');
}


static inline bool IsWordChar(int ch) {
  return (ch < 0x80) && (isalnum(ch) || ch == '_' || ch == '#');
}

static inline bool IsWordStart(int ch) {
	return (ch < 0x80) && (isalpha(ch) || ch == '_' || ch == '#');
}

//ColouriseSimpleDoc():
//  This is very close to the original found in LexPython.cxx, but it has
//  generally been simplified due to fewer constructs.
static void ColouriseSimpleDoc(unsigned int startPos, int length, int initStyle,
                           WordList *keywordlists[], Accessor &styler) {

	int endPos = startPos + length;

	// Backtrack to previous line in case need to fix its tab whinging
	int lineCurrent = styler.GetLine(startPos);

  //Start from the beginning of the line.
  startPos = styler.LineStart(lineCurrent);
  if (startPos == 0)
    initStyle = SCE_SIMPLE_DEFAULT;
  else
    initStyle = styler.StyleAt(startPos - 1);

	WordList &keywords = *keywordlists[0];
	WordList &keywords2 = *keywordlists[1];
  WordList &keywords3 = *keywordlists[2];
  WordList &keywords4 = *keywordlists[3];

  int demarcationLine = styler.GetPropertyInt("lexer.simple.currentline");
  
	initStyle = initStyle & 31;

  bool inString = initStyle == SCE_SIMPLE_STRING;

	int spaceFlags = 0;
	styler.IndentAmount(lineCurrent, &spaceFlags, IsComment);
	bool hexadecimal = false;

	StyleContext sc(startPos, endPos - startPos, initStyle, styler);

	int startIndicator = sc.currentPos;

	for (; sc.More(); sc.Forward()) {

		if (sc.atLineEnd) {
      if ((sc.state == SCE_SIMPLE_DEFAULT) || (sc.state == SCE_SIMPLE_STRING)) {
				// Perform colourisation of white space and quoted strings at end of each line to allow
				// tab marking to work inside white space and quoted strings
				sc.SetState(sc.state);
			}

      if (sc.state == SCE_SIMPLE_OLDLINE) {
        sc.SetState(inString ? SCE_SIMPLE_STRING : SCE_SIMPLE_DEFAULT);
      }
      
			lineCurrent++;
      if (!sc.More())
				break;
		}

		bool needEOLCheck = false;

		// Check for a state end
		if (sc.state == SCE_SIMPLE_OPERATOR) {
			sc.SetState(SCE_SIMPLE_DEFAULT);
		} else if (sc.state == SCE_SIMPLE_NUMBER) {
			if (!IsDigit(sc.ch) && !(sc.ch == '.' && IsDigit(sc.chNext)))
      {
				sc.SetState(SCE_SIMPLE_DEFAULT);
			}
		} else if (sc.state == SCE_SIMPLE_IDENTIFIER) {
			if ((sc.ch == '.') || (!IsWordChar(sc.ch))) {
				char s[100];
				sc.GetCurrent(s, sizeof(s));
				int style = SCE_SIMPLE_IDENTIFIER;
				if (keywords.InList(s)) {
					style = SCE_SIMPLE_WORD;
				} else if (keywords2.InList(s)) {
					style = SCE_SIMPLE_WORD2;
				} else if (keywords3.InList(s)) {
					style = SCE_SIMPLE_WORD3;
				} else if (keywords4.InList(s)) {
					style = SCE_SIMPLE_WORD4;
				}

				sc.ChangeState(style);
				sc.SetState(SCE_SIMPLE_DEFAULT);
			}
		} else if (sc.state == SCE_SIMPLE_COMMENTLINE) {
			if (sc.ch == '\r' || sc.ch == '\n') {
				sc.SetState(SCE_SIMPLE_DEFAULT);
			}
		} else if (sc.state == SCE_SIMPLE_STRING) {
      if (IsStringStart(sc.ch)) {
				sc.ForwardSetState(SCE_SIMPLE_DEFAULT);
        inString = false;
				needEOLCheck = true;
			}
		} else if (sc.state == SCE_SIMPLE_OLDLINE) {
      sc.SetState(inString ? SCE_SIMPLE_STRING : SCE_SIMPLE_DEFAULT);
    }

		// State exit code may have moved on to end of line
		if (needEOLCheck && sc.atLineEnd) {
			lineCurrent++;
			styler.IndentAmount(lineCurrent, &spaceFlags, IsComment);
			if (!sc.More())
				break;
		}

		// Check for a new state starting character
    if (sc.state == SCE_SIMPLE_DEFAULT) {
			if (IsDigit(sc.ch) || (sc.ch == '.' && IsDigit(sc.chNext))) {
				if (sc.ch == '0' && (sc.chNext == 'x' || sc.chNext == 'X')) {
					hexadecimal = true;
				} else {
					hexadecimal = false;
				}
				sc.SetState(SCE_SIMPLE_NUMBER);
			} else if (sc.ch == '%') {
				sc.SetState(SCE_SIMPLE_COMMENTLINE);
			} else if (IsOperator(sc.ch)) {
				sc.SetState(SCE_SIMPLE_OPERATOR);
      } else if (IsStringStart(sc.ch)) {
				sc.SetState(SCE_SIMPLE_STRING);
			} else if (IsWordStart(sc.ch)) {
				sc.SetState(SCE_SIMPLE_IDENTIFIER);
			}
		}
    if(styler.GetLine(sc.currentPos) < demarcationLine)
    {
      if(sc.state == SCE_SIMPLE_STRING)
        inString = !inString;

      sc.SetState(SCE_SIMPLE_OLDLINE);
    }
	}
	styler.IndicatorFill(startIndicator, sc.currentPos, indicatorWhitespace, 0);
	sc.Complete();
}

static bool IsCommentLine(int line, Accessor &styler) {
	int pos = styler.LineStart(line);
	int eol_pos = styler.LineStart(line + 1) - 1;
	for (int i = pos; i < eol_pos; i++) {
		char ch = styler[i];
		if (ch == '%')
			return true;
		else if (ch != ' ' && ch != '\t')
			return false;
	}
	return false;
}

static bool IsQuoteLine(int line, Accessor &styler) {
	int style = styler.StyleAt(styler.LineStart(line)) & 31;
	return (style == SCE_SIMPLE_STRING);
}

//FoldSimpleDoc():
//  This is almost verbatim from the LexPython folding code; as such it doesn't really
//  work that well for a 'simple' language, but it does an acceptable job if the indentation
//  used is similar to pythonic indentation.
static void FoldSimpleDoc(unsigned int startPos, int length, int /*initStyle - unused*/,
                      WordList *[], Accessor &styler) {
	const int maxPos = startPos + length;
	const int maxLines = styler.GetLine(maxPos - 1);             // Requested last line
	const int docLines = styler.GetLine(styler.Length() - 1);  // Available last line
	const bool foldComment = styler.GetPropertyInt("fold.simple.comments") != 0;
	const bool foldQuotes = styler.GetPropertyInt("fold.simple.quotes") != 0;

	// Backtrack to previous non-blank line so we can determine indent level
	// for any white space lines (needed esp. within triple quoted strings)
	// and so we can fix any preceding fold level (which is why we go back
	// at least one line in all cases)
	int spaceFlags = 0;
	int lineCurrent = styler.GetLine(startPos);
	int indentCurrent = styler.IndentAmount(lineCurrent, &spaceFlags, NULL);
	while (lineCurrent > 0) {
		lineCurrent--;
		indentCurrent = styler.IndentAmount(lineCurrent, &spaceFlags, NULL);
		if (!(indentCurrent & SC_FOLDLEVELWHITEFLAG) &&
		        (!IsCommentLine(lineCurrent, styler)) &&
		        (!IsQuoteLine(lineCurrent, styler)))
			break;
	}
	int indentCurrentLevel = indentCurrent & SC_FOLDLEVELNUMBERMASK;

	// Set up initial loop state
	startPos = styler.LineStart(lineCurrent);
	int prev_state = SCE_SIMPLE_DEFAULT & 31;
	if (lineCurrent >= 1)
		prev_state = styler.StyleAt(startPos - 1) & 31;
	int prevQuote = foldQuotes && (prev_state == SCE_SIMPLE_STRING);
	int prevComment = 0;
	if (lineCurrent >= 1)
		prevComment = foldComment && IsCommentLine(lineCurrent - 1, styler);

	// Process all characters to end of requested range or end of any triple quote
	// or comment that hangs over the end of the range.  Cap processing in all cases
	// to end of document (in case of unclosed quote or comment at end).
	while ((lineCurrent <= docLines) && ((lineCurrent <= maxLines) || prevQuote || prevComment)) {

		// Gather info
		int lev = indentCurrent;
		int lineNext = lineCurrent + 1;
		int indentNext = indentCurrent;
		int quote = false;
		if (lineNext <= docLines) {
			// Information about next line is only available if not at end of document
			indentNext = styler.IndentAmount(lineNext, &spaceFlags, NULL);
			int style = styler.StyleAt(styler.LineStart(lineNext)) & 31;
			quote = foldQuotes && (style == SCE_SIMPLE_STRING);
		}
		const int quote_start = (quote && !prevQuote);
		const int quote_continue = (quote && prevQuote);
		const int comment = foldComment && IsCommentLine(lineCurrent, styler);
		const int comment_start = (comment && !prevComment && (lineNext <= docLines) &&
		                           IsCommentLine(lineNext, styler) && (lev > SC_FOLDLEVELBASE));
		const int comment_continue = (comment && prevComment);
		if ((!quote || !prevQuote) && !comment)
			indentCurrentLevel = indentCurrent & SC_FOLDLEVELNUMBERMASK;
		if (quote)
			indentNext = indentCurrentLevel;
		if (indentNext & SC_FOLDLEVELWHITEFLAG)
			indentNext = SC_FOLDLEVELWHITEFLAG | indentCurrentLevel;

		if (quote_start) {
			// Place fold point at start of triple quoted string
			lev |= SC_FOLDLEVELHEADERFLAG;
		} else if (quote_continue || prevQuote) {
			// Add level to rest of lines in the string
			lev = lev + 1;
		} else if (comment_start) {
			// Place fold point at start of a block of comments
			lev |= SC_FOLDLEVELHEADERFLAG;
		} else if (comment_continue) {
			// Add level to rest of lines in the block
			lev = lev + 1;
		}

		// Skip past any blank lines for next indent level info; we skip also
		// comments (all comments, not just those starting in column 0)
		// which effectively folds them into surrounding code rather
		// than screwing up folding.

		while (!quote &&
		        (lineNext < docLines) &&
		        ((indentNext & SC_FOLDLEVELWHITEFLAG) ||
		         (lineNext <= docLines && IsCommentLine(lineNext, styler)))) {

			lineNext++;
			indentNext = styler.IndentAmount(lineNext, &spaceFlags, NULL);
		}

		const int levelAfterComments = indentNext & SC_FOLDLEVELNUMBERMASK;
		const int levelBeforeComments = Platform::Maximum(indentCurrentLevel,levelAfterComments);

		// Now set all the indent levels on the lines we skipped
		// Do this from end to start.  Once we encounter one line
		// which is indented more than the line after the end of
		// the comment-block, use the level of the block before

		int skipLine = lineNext;
		int skipLevel = levelAfterComments;

		while (--skipLine > lineCurrent) {
			int skipLineIndent = styler.IndentAmount(skipLine, &spaceFlags, NULL);

			if ((skipLineIndent & SC_FOLDLEVELNUMBERMASK) > levelAfterComments)
				skipLevel = levelBeforeComments;

			int whiteFlag = skipLineIndent & SC_FOLDLEVELWHITEFLAG;

			styler.SetLevel(skipLine, skipLevel | whiteFlag);
		}

		// Set fold header on non-quote/non-comment line
		if (!quote && !comment && !(indentCurrent & SC_FOLDLEVELWHITEFLAG) ) {
			if ((indentCurrent & SC_FOLDLEVELNUMBERMASK) < (indentNext & SC_FOLDLEVELNUMBERMASK))
				lev |= SC_FOLDLEVELHEADERFLAG;
		}

		// Keep track of triple quote and block comment state of previous line
		prevQuote = quote;
		prevComment = comment_start || comment_continue;

		// Set fold level for this line and move to next line
		styler.SetLevel(lineCurrent, lev);
		indentCurrent = indentNext;
		lineCurrent = lineNext;
	}

	// NOTE: Cannot set level of last line here because indentCurrent doesn't have
	// header flag set; the loop above is crafted to take care of this case!
}


static const char * const simpleWordListDesc[] = {
	"Keywords_0",
  "Keywords_1",
  "Keywords_2",
  "Keywords_3",
};

LexerModule lmSimple(SCLEX_SIMPLE, ColouriseSimpleDoc, "simple", FoldSimpleDoc, simpleWordListDesc);

