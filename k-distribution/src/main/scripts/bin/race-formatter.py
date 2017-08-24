#!/usr/bin/env python3
"""Parse race reports and display involved rules for each race"""
import sys
import argparse
import re
import string

SOURCE_PATTERN = 'Source\\(([^)]*)\\):Location\\(([0-9]*),[0-9]*,([0-9]*),[0-9]*\\)'
RACE_PATTERN = re.compile(
    'Race detected between rules at {s:s} and {s:s}\\.'.format(s=SOURCE_PATTERN))


class Rule(object):
    """Rule representation"""

    def __init__(self, filename, start, end):
        """

        :param filename: Path to a file containing the rule
        :param start: line at which the rule starts
        :param end: line at which the rule ends
        """
        self.__filename = filename
        self.__start = start
        self.__end = end

    def __gt__(self, other):
        return self.__filename > other.filename or (
            self.__filename == other.filename and self.__start > other.start)

    def __repr__(self):
        indent = " " * 2
        return "{i:s}{r:s}    at file://{f:s}#{l:s}\n".format(
            i=indent,
            r=indent.join(Rule.__lines_from_file(
                self.__filename, self.__start, self.__end)),
            f=self.__filename,
            l=self.__start)

    def __eq__(self, other):
        return self.__filename == other.filename and self.__start == other.start

    def __ne__(self, other):
        return not self.__eq__(other)

    def __hash__(self):
        return hash((self.__filename, self.__start))

    @staticmethod
    def __first_non_space(hay):
        """Finds first non-space position"""
        return next(i for i, c in enumerate(hay) if c not in string.whitespace)

    @staticmethod
    def __lines_from_file(filename, start, end):
        with open(filename) as fstr:
            Rule.__lines_from_stream(fstr, start, end)

    @staticmethod
    def __lines_from_stream(fstr, start, end):
        """Returns the collection of lines with indexes between start and end in given file"""
        for i, line in enumerate(fstr):
            if i == int(end):
                break
            elif i >= int(start) - 1:
                if i == int(start) - 1:
                    indent = Rule.__first_non_space(line)
                idx = Rule.__first_non_space(line)
                if idx > indent:
                    idx = indent
                yield line[idx:]


class Race(object):
    """Race Representation"""

    def __init__(self, rule1, rule2):
        if rule1 > rule2:
            self.__rule2 = rule2
            self.__rule1 = rule1
        else:
            self.__rule1 = rule1
            self.__rule2 = rule2

    def __eq__(self, other):
        return self.__rule1 == other.rule1 and self.__rule2 == other.rule2

    def __ne__(self, other):
        return not self.__eq__(other)

    def __hash__(self):
        return hash((self.__rule1, self.__rule2))

    def __repr__(self):
        return "Race detected between\n{r1:s}and\n{r2:s}\n".format(r1=str(self.__rule1), r2=str(self.__rule2))


def load_race(line):
    """Loads one race from the given argument"""
    match = re.search(RACE_PATTERN, line)
    if match is not None:
        race = Race(Rule(match.group(1), match.group(2), match.group(3)),
                    Rule(match.group(4), match.group(5), match.group(6)))
        return race


def load_races(fstr):
    """Loads all races from the given file"""
    races = set()
    for line in fstr:
        race = load_race(line)
        if race is not None and race not in races:
            races.add(race)
            yield race


def main(argv):
    """Main method"""
    parser = argparse.ArgumentParser(
        description="""
        Parses a file containing race descriptions obtained from executing
        definitions compiled using `kompile --check-races`
        and produces a race report containing the rules involved for each race.
        """
    )
    parser.add_argument("-o", "--output", help="output file",
                        default="/dev/stdout")
    parser.add_argument("input", help="input file")
    args = parser.parse_args(argv[1:])
    with open(args.output, "wt") as ostr:
        with open(args.input) as istr:
            for race in load_races(istr):
                ostr.write(str(race))


if __name__ == "__main__":
    main(sys.argv)
