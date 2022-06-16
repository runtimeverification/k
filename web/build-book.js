const path = require("path");
const fs = require("fs");
const { buildBook } = require("k-web-theme");

const tocFilePath = path.resolve(__dirname, "./toc.md");
const projectDirectoryPath = path.resolve(__dirname, "../");
const websiteDirectory = path.resolve(__dirname, "./public_content/");

async function main() {
  const out = await buildBook(tocFilePath, projectDirectoryPath);
  fs.mkdirSync(path.resolve(websiteDirectory, "./exports/"), {
    recursive: true,
  });
  fs.copyFileSync(out.epub, path.join(websiteDirectory, "./exports/K.epub"));
  fs.copyFileSync(out.pdf, path.join(websiteDirectory, "./exports/K.pdf"));
  fs.copyFileSync(out.mobi, path.join(websiteDirectory, "./exports/K.mobi"));
  fs.copyFileSync(out.html, path.join(websiteDirectory, "./exports/K.html"));
  process.exit(0);
}

main();
