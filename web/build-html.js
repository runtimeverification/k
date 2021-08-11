const { cleanUpFiles, generatePagesFromMarkdownFiles } = require("k-web-theme");
const path = require("path");
const fs = require("fs");

cleanUpFiles(path.resolve(__dirname, "./public_content/"));

const tutorialTemplate = fs
  .readFileSync("./static_content/html/tutorial_template.html")
  .toString("utf-8");
const pageTemplate = fs
  .readFileSync("./static_content/html/page_template.html")
  .toString("utf-8");
generatePagesFromMarkdownFiles({
  globPattern: path.resolve(__dirname, "../k-distribution/") + "/**/*.md",
  globOptions: {},
  origin: "https://github.com/kframework/k/tree/master/",
  sourceDirectory: path.resolve(__dirname, "../k-distribution/"),
  outputDirectory: path.resolve(__dirname, "./public_content/k-distribution/"),
  websiteDirectory: path.resolve(__dirname, "./public_content/"),
  websiteOrigin: "https://kframework.org",
  includeFileBasePath: path.resolve(__dirname, "./static_content/html/"),
  template: tutorialTemplate,
});
generatePagesFromMarkdownFiles({
  globPattern: path.resolve(__dirname, "./pages/") + "/**/*.md",
  globOptions: {},
  origin: "https://github.com/kframework/k/tree/master/",
  sourceDirectory: path.resolve(__dirname, "./pages/"),
  outputDirectory: path.resolve(__dirname, "./public_content/"),
  websiteDirectory: path.resolve(__dirname, "./public_content/"),
  websiteOrigin: "https://kframework.org",
  includeFileBasePath: path.resolve(__dirname, "./static_content/html/"),
  template: pageTemplate,
});
generatePagesFromMarkdownFiles({
  globPattern: path.resolve(__dirname, "../") + "/USER_MANUAL.md",
  globOptions: {},
  origin: "https://github.com/kframework/k/tree/master/",
  sourceDirectory: path.resolve(__dirname, "../"),
  outputDirectory: path.resolve(__dirname, "./public_content/"),
  websiteDirectory: path.resolve(__dirname, "./public_content/"),
  websiteOrigin: "https://kframework.org",
  includeFileBasePath: path.resolve(__dirname, "./static_content/html/"),
  template: pageTemplate,
});
