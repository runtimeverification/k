const fs = require("fs");
const path = require("path");
const MarkdownIt = require("markdown-it");
const glob = require("glob");

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
  pattern,
  sourceDirectory,
  outputDirectory,
  template = ""
) {
  const files = glob.sync(pattern);
  for (let i = 0; i < files.length; i++) {
    const file = files[i];
    const targetFilePath = path.resolve(
      path.resolve(
        outputDirectory,
        path.relative(sourceDirectory, path.dirname(file))
      ),
      path.basename(file).match(/^(index|README)\.md$/i)
        ? "index.html"
        : `${path.basename(file).replace(/\.md$/, "")}/index.html`
    );
    let markdown = fs.readFileSync(file).toString("utf-8");
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

function cleanUpFiles() {
  fs.rmdirSync(path.join(__dirname, "./public_content/k-distribution"), {
    recursive: true,
  });

  const files = glob.sync(
    path.join(__dirname, "./public_content/") + "/**/*.html"
  );
  files.forEach((file) => {
    fs.unlinkSync(file);
    const dirPath = path.dirname(file);
    const filesInside = fs.readdirSync(dirPath);
    if (!filesInside.length) {
      fs.rmdirSync(dirPath, { recursive: true });
    }
  });
}

for (file in files) {
  generateOutputWebpage(fs.readFileSync(file).toString("utf-8"), files[file]);
}

cleanUpFiles();
const tutorialTemplate = fs
  .readFileSync("./static_content/html/tutorial_template.html")
  .toString("utf-8");
const pageTemplate = fs
  .readFileSync("./static_content/html/page_template.html")
  .toString("utf-8");
generatePagesFromMarkdownFiles(
  path.resolve(__dirname, "../k-distribution/") + "/**/*.md",
  path.resolve(__dirname, "../k-distribution/"),
  path.resolve(__dirname, "./public_content/k-distribution/"),
  tutorialTemplate
);
generatePagesFromMarkdownFiles(
  path.resolve(__dirname, "./pages/") + "/**/*.md",
  path.resolve(__dirname, "./pages/"),
  path.resolve(__dirname, "./public_content/"),
  pageTemplate
);
generatePagesFromMarkdownFiles(
  path.resolve(__dirname, "../") + "/pending-documentation.md",
  path.resolve(__dirname, "../"),
  path.resolve(__dirname, "./public_content/"),
  pageTemplate
);
