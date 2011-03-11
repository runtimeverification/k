var Riot;
if (typeof load !== 'undefined') {
  load('riot.js');
} else if (typeof require !== 'undefined') {
  Riot = require('./riot').Riot;
}

Riot.run(function() {
  context('1. Basic riot functionality', function() {
    given('1.1 some simple equality tests', function() {
      setup(function() {
        return true;
      });

      asserts('a simple truth test should return true', true).isTrue();
      asserts('a false test returns false', false).isFalse();
      asserts('isNull is null', null).isNull();
      asserts('no chained test expected a value', true);
    });

    given('1.1.2 some string tests', function() {
      should('compare strings with equals', 'test string').equals('test string');
      should('match expressions with matches', 'test').matches(/test/);
    });

    given('1.1.3 a context concerned with functions', function() {
      asserts('asserts() should allow functions to be compared', function() {
        return 'test string';
      }).equals('test string');
    });

    given('1.1.4 an example that requires a variable', function() {
      var user = { name: 'Grumble' };

      should('get evaluated before the assertions', user.name).equals('Grumble');
    });

    given('1.1.5 some objects that need type checks', function() {
      asserts('a string should be a String', 'String').kindOf('String');
      asserts('an array should be an Array', [1, 2, 3]).kindOf('Array');
      asserts('an array should be an Array', null).typeOf('null');
    });

    given('1.1.6 some exceptions', function() {
      asserts('this should raise ExampleError', function() { throw('ExampleError'); }).raises('ExampleError');
    });
  });

  context('1.2. Equality', function() {
    given('1.2.1. isEqual()', function () {
      should('return falsy when an empty object is supplied as the first param', function() {
        return ! Riot.Assertion.prototype.isEqual({}, {a: 'a', b: 'b'});
      }).isTrue();
    });
  });

  context('1.3 Yet another context', function() {
    asserts('equals should compare strings as expected', 'test string').equals('test string');
  });

  context('1.4 End', function() {
    asserts('this test should appear at the end', true);
  });
});
