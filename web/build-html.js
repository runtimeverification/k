const {
  generatePagesFromMarkdownFiles,
  convertSidebarToCToHTML,
} = require("k-web-theme");
const path = require("path");
const fs = require("fs");

const tutorialTemplate = fs
  .readFileSync("./static_content/html/tutorial_template.html")
  .toString("utf-8");
const pageTemplate = fs
  .readFileSync("./static_content/html/page_template.html")
  .toString("utf-8");
const tocMarkdown = fs.readFileSync("./toc.md").toString("utf-8");
const tocHTML = convertSidebarToCToHTML(tocMarkdown, (url) => {
  return url
    .replace(/(index|README)\.md$/, "")
    .replace(/\.md$/, "/")
    .replace(/\/web\/pages\//, "/")
    .replace(/^\//, "{{$ROOT}}/")
    .replace(/\/+$/, "/");
});

generatePagesFromMarkdownFiles({
  globPattern: path.resolve(__dirname, "../k-distribution/") + "/**/*.md",
  globOptions: {},
  origin: "https://github.com/runtimeverification/k/tree/master/",
  sourceDirectory: path.resolve(__dirname, "../k-distribution/"),
  outputDirectory: path.resolve(__dirname, "./public_content/k-distribution/"),
  websiteDirectory: path.resolve(__dirname, "./public_content/"),
  websiteOrigin: "https://kframework.org",
  includeFileBasePath: path.resolve(__dirname, "./static_content/html/"),
  template: tutorialTemplate,
  variables: {
    TOC: tocHTML,
  },
});
generatePagesFromMarkdownFiles({
  globPattern: path.resolve(__dirname, "./pages/") + "/**/*.md",
  globOptions: {},
  origin: "https://github.com/runtimeverification/k/tree/master/",
  sourceDirectory: path.resolve(__dirname, "./pages/"),
  outputDirectory: path.resolve(__dirname, "./public_content/"),
  websiteDirectory: path.resolve(__dirname, "./public_content/"),
  websiteOrigin: "https://kframework.org",
  includeFileBasePath: path.resolve(__dirname, "./static_content/html/"),
  template: pageTemplate,
  variables: {
    TOC: tocHTML,
  },
});
generatePagesFromMarkdownFiles({
  globPattern: path.resolve(__dirname, "../docs/") + "/*.md",
  globOptions: {},
  origin: "https://github.com/runtimeverification/k/tree/master/",
  sourceDirectory: path.resolve(__dirname, "../"),
  outputDirectory: path.resolve(__dirname, "./public_content/"),
  websiteDirectory: path.resolve(__dirname, "./public_content/"),
  websiteOrigin: "https://kframework.org",
  includeFileBasePath: path.resolve(__dirname, "./static_content/html/"),
  template: pageTemplate,
  variables: {
    TOC: tocHTML,
  },
});

fs.copyFileSync(
  path.join(__dirname, "../package/nix/install"),
  path.join(__dirname, "./public_content/install")
);
