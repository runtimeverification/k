const fs = require("fs");
const path = require("path");
const MarkdownIt = require("markdown-it");

const md = new MarkdownIt({
  html: true,
  linkify: true,
});

const files = {
  "./static_content/html/404.html": "404.html",
  "./static_content/html/500.html": "500.html",
};

const outPath = "./public_content/";
const basePath = "static_content/html/";
const regexp = /{{(.*)}}/;

/**
 *
 * @param {string} sourceHTML the HTML content
 * @param {string} targetFilePath path relative to current __dirname
 * @param {object} variables variables map
 */
function generateOutputWebpage(sourceHTML, targetFilePath, variables = {}) {
  const filePath = targetFilePath.startsWith("/")
    ? targetFilePath
    : path.join(__dirname, outPath, targetFilePath);
  const dirname = path.dirname(filePath);

  if (!fs.existsSync(dirname)) fs.mkdirSync(dirname, { recursive: true });

  const relative = path.relative(dirname, outPath);

  const resultHTML = sourceHTML
    .split("\n")
    .map((line) => {
      const match = line.match(regexp);
      let content = line;

      if (match && match.length == 2 && !match[1].startsWith("$")) {
        content = fs.readFileSync(basePath + match[1]).toString();
      }

      // Fix assets folder path error for github page
      content = content.replace(/{{\$(.+?)}}/g, (_, variableName) => {
        if (variableName === "ROOT") {
          return relative || ".";
        } else if (variableName in variables) {
          return variables[variableName];
        } else {
          return _;
        }
      });

      return content;
    })
    .join("\n");
  fs.writeFileSync(filePath, resultHTML);
  console.log("Written file: " + filePath);
}

/**
 *
 * @param {string} sourceDirectory
 * @param {string} outputDirectory
 * @param {string} template
 */
function generatePagesFromMarkdownFiles(
  sourceDirectory,
  outputDirectory,
  template = ""
) {
  const helper = (dirPath) => {
    for (const file of fs.readdirSync(dirPath)) {
      if (fs.statSync(path.resolve(dirPath, file)).isDirectory()) {
        helper(path.resolve(dirPath, file));
      } else if (file.endsWith(".md")) {
        const targetFilePath = path.resolve(
          path.resolve(
            outputDirectory,
            path.relative(sourceDirectory, dirPath)
          ),
          file.match(/^(index|README)\.md$/i)
            ? "index.html"
            : `${file.replace(/\.md$/, "")}/index.html`
        );
        let markdown = fs
          .readFileSync(path.resolve(dirPath, file))
          .toString("utf-8");

        if (
          markdown.startsWith("---") &&
          /* tslint:disable-next-line:no-conditional-assignment */
          (endFrontMatterOffset = markdown.indexOf("\n---")) > 0
        ) {
          markdown = markdown
            .slice(endFrontMatterOffset + 4)
            .replace(/^[ \t]*\n/, "");
        }

        const html = md.render(markdown);

        generateOutputWebpage(template, targetFilePath, {
          TITLE: targetFilePath,
          MARKDOWN_HTML: html,
        });
      }
    }
  };
  helper(sourceDirectory, template);
}

for (file in files) {
  generateOutputWebpage(fs.readFileSync(file).toString("utf-8"), files[file]);
}

fs.rmdirSync(path.join(__dirname, "./public_content/k-distribution"), {
  recursive: true,
});
const tutorialTemplate = fs
  .readFileSync("./static_content/html/tutorial_template.html")
  .toString("utf-8");
const pageTemplate = fs
  .readFileSync("./static_content/html/page_template.html")
  .toString("utf-8");
generatePagesFromMarkdownFiles(
  path.resolve(__dirname, "../k-distribution/tutorial/"),
  path.resolve(__dirname, "./public_content/k-distribution/tutorial/"),
  tutorialTemplate
);
generatePagesFromMarkdownFiles(
  path.resolve(__dirname, "./pages/"),
  path.resolve(__dirname, "./public_content/"),
  pageTemplate
);
