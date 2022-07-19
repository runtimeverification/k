import json
from argparse import ArgumentParser
from sys import stdin

from pyk.kast import KDefinition, KRule, KSentence


def main():
    parser = create_argument_parser()
    args = parser.parse_args()

    with open(args.compiled_json, 'r') as f:
        json_data = json.load(f)

    format = json_data['format']
    version = json_data['version']
    term = json_data['term']

    input_definition = KDefinition.from_dict(term)
    output_definition = transform_definition(input_definition)

    print(json.dumps({
        'format': format,
        'version': version,
        'term': output_definition.to_dict(),
    }))


def create_argument_parser() -> ArgumentParser:
    parser = ArgumentParser(description='Transform rules of a compiled K definition')
    parser.add_argument('compiled_json', type=str, help='Path to compiled.json')
    return parser


def transform_definition(definition: KDefinition) -> KDefinition:
    return (
        definition.let(modules=(
            module.let(sentences=(
                transform_sentence(sentence) for sentence in module.sentences
            )) for module in definition.modules
        ))
    )


def transform_sentence(sentence: KSentence) -> KSentence:
    return transform_rule(sentence) if type(sentence) is KRule else sentence

def transform_rule(rule: KRule) -> KRule:
    # TODO
    return rule


if __name__ == "__main__":
   main()
