/**
 *
 * @param {HLJSApi} hljs
 */
module.exports = function (hljs) {
  //Does not support unicode characters (should be replaced by \p{L} when possible)
  var unicodeWord =
    "^:\\(\\)*\\/\\|\\.=\\$\\<\\>\\#\\'\\[\\]\"\\-\\!\\%\\&\\~\\+\\,\\;\\n\\r";

  var KEYWORDS = {
    className: "keyword",
    begin:
      "[\\s]*\\b(syntax|rule|Id|Int|Bool|String|configuration|imports|require|Token|Lexer|Float|requires|Kresult|context|module|endmodule)\\b",
  };

  var LITERALS = {
    className: "literal",
    begin:
      "\\b(strict|avoid|prefer|bracket|non-assoc|seqstrict|left|right|macro|token|notInRules|autoReject|structural|latex|binder)",
  };

  var DATE = {
    className: "literal",
    begin: "![0-9]+",
    end: "!",
  };

  var NUMBERS = {
    className: "number",
    begin:
      "(-?)(\\b0[xX][a-fA-F0-9]+|(\\b[\\d]+(\\.[\\d]*)?|\\.[\\d]+)([eE][-+]?[\\d]+)?)(?!D)",
  };

  var STRINGS = {
    className: "string",
    begin: '"',
    end: '"',
    illegal: "\\n",
    contains: [hljs.BACKSLASH_ESCAPE],
    relevance: 0,
  };

  var INLINE_COMMENT = hljs.COMMENT("//", "[^\\\\]$");

  return {
    aliases: ["k"],
    keyword: KEYWORDS,
    contains: [
      INLINE_COMMENT, // single-line comments
      hljs.C_BLOCK_COMMENT_MODE, // comment blocks
      DATE,
      KEYWORDS,
      STRINGS,
      NUMBERS,
      LITERALS,
    ],
  };
};
