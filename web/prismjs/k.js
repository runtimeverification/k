module.exports = function (Prism) {
  Prism.languages.k = {
    comment: [
      {
        pattern: /(^|[^\\])\/\*[\s\S]*?(?:\*\/|$)/,
        lookbehind: true,
      },
      {
        pattern: /(^|[^\\:])\/\/.*/,
        lookbehind: true,
        greedy: true,
      },
    ],
    string: {
      pattern: /(["'])(?:\\(?:\r\n|[\s\S])|(?!\1)[^\\\r\n])*\1/,
      greedy: true,
    },
    "class-name": /\b(?:strict|avoid|prefer|bracket|non-assoc|seqstrict|left|right|macro|token|notInRules|autoReject|structural|latex|binder|klabel|format)\b/,
    keyword: /\b(?:syntax|rule|Id|Int|Bool|String|configuration|imports|require|Token|Lexer|Float|requires|Kresult|context|module|endmodule)\b/,
    boolean: /\b(?:true|false)\b/,
    number: /\b0x[\da-f]+\b|(?:\b\d+\.?\d*|\B\.\d+)(?:e[+-]?\d+)?/i,
    operator: /[<>]=?|[!=]=?=?|--?|\+\+?|&&?|\|\|?|[?*/~^%]/,
    punctuation: /[{}[\];(),.:]/,
  };
};
