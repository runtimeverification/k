/* ---------------------------------------------
 common scripts
 --------------------------------------------- */

(function () {
  "use strict"; // use strict to start

  /* ---------------------------------------------
     WOW init
     --------------------------------------------- */

  new WOW().init();

  $(document).ready(function () {
    // Sidebar menu
    $(".bd-search-docs-toggle").click(() => {
      if ($(".bd-search-docs-toggle").hasClass("collapsed")) {
        $(".bd-sidebar > nav").addClass("show");
        $(".bd-search-docs-toggle").removeClass("collapsed");
      } else {
        $(".bd-sidebar > nav").removeClass("show");
        $(".bd-search-docs-toggle").addClass("collapsed");
      }
    });

    // Sanitize links
    $("a").each((index, anchorElement) => {
      try {
        const href = new URL(anchorElement.href);
        if (href.host === location.host) {
          if (anchorElement.href.endsWith(".md")) {
            console.log(anchorElement.getAttribute("href"));
            let href = anchorElement.getAttribute("href");
            if (href.startsWith("../") && !href.match(/(index|README)\.md$/)) {
              href = "../" + href;
            }
            anchorElement.setAttribute(
              "href",
              href.match(/(index|README)\.md$/)
                ? href.replace(/(index|README)\.md$/, "")
                : href.replace(/\.md$/, "/")
            );
          }
        } else {
          anchorElement.setAttribute("target", "_blank");
          anchorElement.setAttribute("rel", "noopener");
        }
      } catch (error) {}
    });

    // Search box
    $("#search-box").keydown((event) => {
      if (event.which === 13) {
        event.stopPropagation();
        event.preventDefault();
        window.open(
          `https://www.google.com/search?q=site:${
            location.hostname.match(/\.github\.io/)
              ? location.hostname + "/k"
              : location.hostname
          }%20${encodeURIComponent($("#search-box").val())}`,
          "_blank"
        );
      }
    });
  });
})(jQuery);
