/*jslint white: false plusplus: false onevar: false browser: true evil: true*/
/*riotGlobal window: true*/
(function(riotGlobal) {
  var Riot = {
    results:  [],
    contexts: [],

    run: function(tests) {
      switch (Riot.detectEnvironment()) {
        case 'xpcomcore':
          Riot.formatter = new Riot.Formatters.XPComCore();
          Riot.runAndReport(tests);
          Sys.exit(Riot.exitCode);
          break;

        case 'rhino':
          Riot.formatter = new Riot.Formatters.Text();
          Riot.runAndReport(tests);
          java.lang.System.exit(Riot.exitCode);
          break;

        case 'node':
          Riot.formatter = new Riot.Formatters.Text();
          Riot.runAndReport(tests);
          // TODO: exit with exit code from riot
          break;

        case 'non-browser-interpreter':
          Riot.formatter = new Riot.Formatters.Text();
          Riot.runAndReport(tests);
          if (typeof quit !== 'undefined') {
            quit(Riot.exitCode);
          }
          break;

        case 'browser':
          Riot.formatter = new Riot.Formatters.HTML();
          if (typeof window.onload === 'undefined' || window.onload == null) {
            Riot.browserAutoLoad(tests);
          }
          break;
      }
    },

    browserAutoLoad: function(tests) {
      var timer;
      function fireContentLoadedEvent() {
        if (document.loaded) return;
        if (timer) window.clearTimeout(timer);
        document.loaded = true;

        if (Riot.requiredFiles.length > 0) {
          Riot.loadBrowserScripts(Riot.requiredFiles, tests);
        } else {
          Riot.runAndReport(tests);
        }
      }

      function checkReadyState() {
        if (document.readyState === 'complete') {
          document.detachEvent('readystatechange', checkReadyState);
          fireContentLoadedEvent();
        }
      }

      function pollDoScroll() {
        try { document.documentElement.doScroll('left'); }
        catch(e) {
          timer = setTimeout(pollDoScroll, 10);
          return;
        }
        fireContentLoadedEvent();
      }

      if (document.addEventListener) {
        document.addEventListener('DOMContentLoaded', fireContentLoadedEvent, false);
      } else {
        document.attachEvent('readystatechange', checkReadyState);
        if (window == top)
          timer = setTimeout(pollDoScroll, 10);
      }

      window.onload = fireContentLoadedEvent;
    },

    loadBrowserScripts: function(files, tests) {
      var i, file;

      function loadBrowserScript(src, callback) {
        var script = document.createElement('script'),
            head = document.getElementsByTagName('head')[0],
            readyState;
        script.setAttribute('type', 'text/javascript');
        script.setAttribute('src', src);
        script.onload = script.onreadystatechange = function() {
          if (!(readyState = script.readyState) || /loaded|complete/.test(readyState)) {
            script.onload = script.onreadystatechange = null;
            head.removeChild(script);
            if (callback) {
              setTimeout(callback, 1);
            }
          }
        };
        
        head.insertBefore(script, head.firstChild);
      }

      if (files.length > 1) {
        file = files[0];
        loadBrowserScript(file, function() { Riot.loadBrowserScripts(files.slice(1), tests); });
      } else {
        file = files[0];
        loadBrowserScript(file, function() { Riot.runAndReport(tests); });
      }
    },

    load: function() {
      switch (Riot.detectEnvironment()) {
        case 'xpcomcore':
        case 'rhino':
        case 'non-browser-interpreter':
          load(arguments[0]);
          break;
        case 'node':
          // Evaluate the required code in the global context, like load() would
          global.eval.call(global, Riot.node.fs.readFileSync(arguments[0]).toString());
          break;
        case 'browser':
          var script = document.createElement('script'),
              head = document.getElementsByTagName('head');
          script.setAttribute('type', 'text/javascript');
          script.setAttribute('src', arguments[0]);
          head[0].insertBefore(script, head.firstChild);
          break;
      }
    },

    requiredFiles: [],

    indexOf: function(array, value) {
      for (var i = 0; i < array.length; i++) {
        if (array[i] === value) {
          return i;
        }
      }
      return -1;
    },

    require: function() {
      if (this.indexOf(this.requiredFiles, arguments[0]) == -1) {
        this.requiredFiles.push(arguments[0]);
        if (Riot.detectEnvironment() !== 'browser') {
          this.load(arguments[0]);
        }
      }
    },

    detectEnvironment: function() {
      if (typeof this.env !== 'undefined') {
        return this.env;
      }

      this.env = (function() {
        if (typeof XPCOMCore !== 'undefined') {
          Riot.puts = print;
          return 'xpcomcore';
        } else if (typeof window === 'undefined' && typeof java !== 'undefined') {
          Riot.puts = print;
          return 'rhino';
        } else if (typeof exports !== 'undefined') {
          // TODO: Node should be checked more thoroughly
          Riot.node = {
            fs: require('fs'),
            sys: require('sys')
          }

          Riot.puts = Riot.node.sys.puts;

          return 'node';
        } else if (typeof window === 'undefined') {
          Riot.puts = print;
          return 'non-browser-interpreter';
        } else {
          return 'browser';
        }
      })();

      return this.env;
    },

    runAndReport: function(tests) {
      this.running = true;
      var benchmark = Riot.Benchmark.run(1, function() { Riot.runAllContexts(tests); });
      Riot.formatter.separator();
      Riot.summariseAllResults();
      Riot.formatter.line(benchmark);
      this.running = false;
    },

    runAllContexts: function(tests) {
      if (typeof tests !== 'undefined') {
        this.withDSL(tests)();
      }

      for (var i = 0; i < this.contexts.length; i++) {
        this.contexts[i].run();
      }
    },

    functionBody: function(fn) {
      return '(' + fn.toString().replace(/\s+$/, '') + ')()';
    },

    withDSL: function(fn, context) {
      var body = this.functionBody(fn),
          f    = new Function('context', 'given', 'asserts', 'should', 'setup', 'teardown', body),
          args = [
            Riot.context,
            Riot.given,
            function() { return context.asserts.apply(context, arguments); },
            function() { return context.should.apply(context, arguments); },
            function() { return context.setup.apply(context, arguments); },
            function() { return context.teardown.apply(context, arguments); }
          ];

      return function() { f.apply(Riot, args); };
    },

    context: function(title, callback) {
      var context = new Riot.Context(title, callback);

      if (this.running) {
        context.run();
      } else {
        Riot.contexts.push(context);
      }

      return context;
    },

    given: function(title, callback) {
      title = 'Given ' + title;
      return Riot.context(title, callback);
    },

    summariseAllResults: function() { return this.summarise(this.results); },

    summarise: function(results) {
      var failures = 0;
      for (var i = 0; i < results.length; i++) {
        if (!results[i].pass) { failures++; }
      }
      this.formatter.line(results.length + ' assertions: ' + failures + ' failures');
      this.exitCode = failures > 0 ? 1 : 0;
    },

    addResult: function(context, assertion, pass) {
      var result = {
        assertion: assertion,
        pass:      pass,
        context:   context
      };
      this.results.push(result);
    }
  };

  Riot.Benchmark = {
    results: [],

    addResult: function(start, end) {
      this.results.push(end - start);
    },

    displayResults: function() {
      var total   = 0,
          seconds = 0,
          i       = 0;
      for (i = 0; i < this.results.length; i++) {
        total += this.results[i];
      }
      seconds = total / 1000;
      return 'Elapsed time: ' + total + 'ms (' + seconds + ' seconds)';
    },

    run: function(times, callback) {
      this.results = [];
      for (var i = 0; i < times; i++) {
        var start = new Date(),
            end   = null;
        callback();
        end = new Date();
        this.addResult(start, end);
      }
      return this.displayResults();
    }
  };

  Riot.Formatters = {
    HTML: function() {
      function display(html) {
        var results = document.getElementById('test-results');
        results.innerHTML += html;
      }

      this.line = function(text) {
        display('<p>' + text + '</p>');
      };

      this.pass = function(message) {
        display('<p class="pass">' + message + '</p>');
      };

      this.fail = function(message) {
        display('<p class="fail">' + message + '</p>');
      };

      this.error = function(message, exception) {
        this.fail(message);
        display('<p class="exception">Exception: ' + exception + '</p>');
      };

      this.context = function(name) {
        display('<h3>' + name + '</h3>');
      };

      this.given = function(name) {
        display('<h4>' + name + '</h4>');
      };

      this.separator = function() {
        display('<hr />');
      };
    },

    Text: function() {
      function display(text) {
        Riot.puts(text);
      }

      this.line = function(text) {
        display(text);
      };

      this.pass = function(message) {
        this.line('  +\033[32m ' + message + '\033[0m');
      };

      this.fail = function(message) {
        this.line('  -\033[31m ' + message + '\033[0m');
      };

      this.error = function(message, exception) {
        this.fail(message);
        this.line('  Exception: ' + exception);
      };

      this.context = function(name) {
        this.line(name);
      };

      this.given = function(name) {
        this.line(name);
      };

      this.separator = function() {
        this.line('');
      };
    },

    XPComCore: function() {
      var formatter = new Riot.Formatters.Text();
      formatter.line = function(text) {
        puts(text);
      };
      return formatter;
    }
  };

  Riot.Context = function(name, callback) {
    this.name             = name;
    this.callback         = callback;
    this.assertions       = [];
  };

  Riot.Context.prototype = {
    asserts: function(name, result) {
      var assertion = new Riot.Assertion(this.name, name, result);
      this.assertions.push(assertion);
      return assertion;
    },

    should: function(name, result) {
      return this.asserts('should ' + name, result);
    },

    setup: function(setupFunction) {
      this.setupFunction = setupFunction;
    },

    teardown: function(teardownFunction) {
      this.teardownFunction = teardownFunction;
    },

    runSetup: function() {
      if (typeof this.setupFunction !== 'undefined') {
        return this.setupFunction();
      }
    },

    runTeardown: function() {
      if (typeof this.teardownFunction !== 'undefined') {
        return this.teardownFunction();
      }
    },

    formatContextName: function() {
      if (this.name.match(/^Given/)) {
        Riot.formatter.given(this.name);
      } else {
        Riot.formatter.context(this.name);
      }
    },

    run: function() {
      this.formatContextName();
      Riot.withDSL(this.callback, this)();
      this.runSetup();
      for (var i = 0; i < this.assertions.length; i++) {
        var pass = false,
            assertion = this.assertions[i];
        try {
          assertion.run();
          pass = true;
          Riot.formatter.pass(assertion.name);
        } catch (e) {
          if (typeof e.name !== 'undefined' && e.name === 'Riot.AssertionFailure') {
            Riot.formatter.fail(e.message);
          } else {
            Riot.formatter.error(assertion.name, e);
          }
        }

        Riot.addResult(this.name, assertion.name, pass);
      }
      this.runTeardown();
    }
  };

  Riot.AssertionFailure = function(message) {
    var error = new Error(message);
    error.name = 'Riot.AssertionFailure';
    return error;
  };

  Riot.Assertion = function(contextName, name, expected) {
    this.name          = name;
    this.expectedValue = expected;
    this.contextName   = contextName;
    this.kindOf        = this.typeOf;
    this.isTypeOf      = this.typeOf;

    this.setAssertion(function(actual) {
      if ((actual() === null) || (actual() === undefined)) {
        throw(new Riot.AssertionFailure("Expected a value but got '" + actual() + "'"));
      }
    });
  };

  Riot.Assertion.prototype = {
    setAssertion: function(assertion) {
      this.assertion = assertion;
    },

    run: function() {
      var that = this;
      this.assertion(function() { return that.expected(); });
    },

    fail: function(message) {
      throw(new Riot.AssertionFailure(this.name + ': ' + message));
    },

    expected: function() {
      if (typeof this.expectedMemo === 'undefined') {
        if (typeof this.expectedValue === 'function') {
          try {
            this.expectedMemo = this.expectedValue();
          } catch (exception) {
            this.expectedValue = exception;
          }
        } else {
          this.expectedMemo = this.expectedValue;
        }
      }
      return this.expectedMemo;
    },

    // Based on http://github.com/visionmedia/jspec/blob/master/lib/jspec.js
    // Short-circuits early, can compare arrays
    isEqual: function(a, b) {
      if (typeof a != typeof b) return;
      if (a === b) return true;
      if (a instanceof RegExp) {
        return a.toString() === b.toString();
      }
      if (a instanceof Date) {
        return Number(a) === Number(b);
      }
      if (typeof a != 'object') return;
      if (a.length !== undefined) {
        if (a.length !== b.length) {
          return;
        } else {
          for (var i = 0, len = a.length; i < len; ++i) {
            if (!this.isEqual(a[i], b[i])) {
              return;
            }
          }
        }
      }
      for (var key in b) {
        if (!this.isEqual(a[key], b[key])) {
          return;
        }
      }
      return true;
    },

    /* Assertions */
    equals: function(expected) {
      this.setAssertion(function(actual) {
        if (!this.isEqual(actual(), expected)) {
          this.fail(expected + ' does not equal: ' + actual());
        }
      });
    },

    matches: function(expected) {
      this.setAssertion(function(actual) {
        if (!expected.test(actual())) {
          this.fail("Expected '" + actual() + "' to match '" + expected + "'");
        }
      });
    },

    raises: function(expected) {
      this.setAssertion(function(actual) {
        try {
          actual();
          return;
        } catch (exception) {
          if (expected !== exception) {
            this.fail('raised ' + exception  + ' instead of ' + expected);
          }
        }
        this.fail('did not raise ' + expected);
      });
    },

    typeOf: function(expected) {
      this.setAssertion(function(actual) {
        var t = typeof actual();
        if (t === 'object') {
          if (actual()) {
            if (typeof actual().length === 'number' &&
                !(actual.propertyIsEnumerable('length')) &&
                typeof actual().splice === 'function') {
              t = 'array';
            }
          } else {
            t = 'null';
          }
        }

        if (t !== expected.toLowerCase()) {
          this.fail(expected + ' is not a type of ' + actual());
        }
      });
    },

    isTrue: function() {
      this.setAssertion(function(actual) {
        if (actual() !== true) {
          this.fail(actual() + ' was not true');
        }
      });
    },

    isFalse: function() {
      this.setAssertion(function(actual) {
        if (actual() !== false) {
          this.fail(actual() + ' was not false');
        }
      });
    },

    isNull: function() {
      this.setAssertion(function(actual) {
        if (actual() !== null) {
          this.fail(actual() + ' was not null');
        }
      });
    },

    isNotNull: function() {
      this.setAssertion(function(actual) {
        if (actual() === null) {
          this.fail(actual() + ' was null');
        }
      });
    }
  };

  if (typeof exports !== 'undefined') {
    exports.Riot = Riot;
  } else if (typeof riotGlobal.Riot === 'undefined') {
    riotGlobal.Riot = Riot;

    if (typeof riotGlobal.load === 'undefined') {
      riotGlobal.load = function() { };
    }
  }
})(typeof window === 'undefined' ? this : window);
