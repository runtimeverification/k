from __future__ import annotations

import sys
from enum import Enum
from typing import TYPE_CHECKING

if TYPE_CHECKING:
    from typing import IO, Final


class Color(Enum):
    ALICE_BLUE = 'AliceBlue'
    ANTIQUE_WHITE = 'AntiqueWhite'
    APRICOT = 'Apricot'
    AQUA = 'Aqua'
    AQUAMARINE = 'Aquamarine'
    AZURE = 'Azure'
    BEIGE = 'Beige'
    BISQUE = 'Bisque'
    BITTERSWEET = 'Bittersweet'
    BLACK = 'black'
    BLANCHED_ALMOND = 'BlanchedAlmond'
    BLUE = 'blue'
    BLUE_GREEN = 'BlueGreen'
    BLUE_VIOLET = 'BlueViolet'
    BRICK_RED = 'BrickRed'
    BROWN = 'brown'
    BURLY_WOOD = 'BurlyWood'
    BURNT_ORANGE = 'BurntOrange'
    CADET_BLUE = 'CadetBlue'
    CARNATION_PINK = 'CarnationPink'
    CERULEAN = 'Cerulean'
    CHARTREUSE = 'Chartreuse'
    CHOCOLATE = 'Chocolate'
    CORAL = 'Coral'
    CORNFLOWER_BLUE = 'CornflowerBlue'
    CORNSILK = 'Cornsilk'
    CRIMSON = 'Crimson'
    CYAN = 'cyan'
    DANDELION = 'Dandelion'
    DARKGRAY = 'darkgray'
    DARK_BLUE = 'DarkBlue'
    DARK_CYAN = 'DarkCyan'
    DARK_GOLDENROD = 'DarkGoldenrod'
    DARK_GRAY = 'DarkGray'
    DARK_GREEN = 'DarkGreen'
    DARK_GREY = 'DarkGrey'
    DARK_KHAKI = 'DarkKhaki'
    DARK_MAGENTA = 'DarkMagenta'
    DARK_OLIVE_GREEN = 'DarkOliveGreen'
    DARK_ORANGE = 'DarkOrange'
    DARK_ORCHID = 'DarkOrchid'
    DARK_RED = 'DarkRed'
    DARK_SALMON = 'DarkSalmon'
    DARK_SEA_GREEN = 'DarkSeaGreen'
    DARK_SLATE_BLUE = 'DarkSlateBlue'
    DARK_SLATE_GRAY = 'DarkSlateGray'
    DARK_SLATE_GREY = 'DarkSlateGrey'
    DARK_TURQUOISE = 'DarkTurquoise'
    DARK_VIOLET = 'DarkViolet'
    DEEP_PINK = 'DeepPink'
    DEEP_SKY_BLUE = 'DeepSkyBlue'
    DIM_GRAY = 'DimGray'
    DIM_GREY = 'DimGrey'
    DODGER_BLUE = 'DodgerBlue'
    EMERALD = 'Emerald'
    FIRE_BRICK = 'FireBrick'
    FLORAL_WHITE = 'FloralWhite'
    FOREST_GREEN = 'ForestGreen'
    FUCHSIA = 'Fuchsia'
    GAINSBORO = 'Gainsboro'
    GHOST_WHITE = 'GhostWhite'
    GOLD = 'Gold'
    GOLDENROD = 'Goldenrod'
    GRAY = 'gray'
    GREEN = 'green'
    GREEN_YELLOW = 'GreenYellow'
    GREY = 'Grey'
    HONEYDEW = 'Honeydew'
    HOT_PINK = 'HotPink'
    INDIAN_RED = 'IndianRed'
    INDIGO = 'Indigo'
    IVORY = 'Ivory'
    JUNGLE_GREEN = 'JungleGreen'
    KHAKI = 'Khaki'
    LAVENDER = 'Lavender'
    LAVENDER_BLUSH = 'LavenderBlush'
    LAWN_GREEN = 'LawnGreen'
    LEMON_CHIFFON = 'LemonChiffon'
    LIGHTGRAY = 'lightgray'
    LIGHT_BLUE = 'LightBlue'
    LIGHT_CORAL = 'LightCoral'
    LIGHT_CYAN = 'LightCyan'
    LIGHT_GOLDENROD = 'LightGoldenrod'
    LIGHT_GOLDENROD_YELLOW = 'LightGoldenrodYellow'
    LIGHT_GRAY = 'LightGray'
    LIGHT_GREEN = 'LightGreen'
    LIGHT_GREY = 'LightGrey'
    LIGHT_PINK = 'LightPink'
    LIGHT_SALMON = 'LightSalmon'
    LIGHT_SEA_GREEN = 'LightSeaGreen'
    LIGHT_SKY_BLUE = 'LightSkyBlue'
    LIGHT_SLATE_BLUE = 'LightSlateBlue'
    LIGHT_SLATE_GRAY = 'LightSlateGray'
    LIGHT_SLATE_GREY = 'LightSlateGrey'
    LIGHT_STEEL_BLUE = 'LightSteelBlue'
    LIGHT_YELLOW = 'LightYellow'
    LIME = 'lime'
    LIME_GREEN = 'LimeGreen'
    LINEN = 'Linen'
    MAGENTA = 'magenta'
    MAHOGANY = 'Mahogany'
    MAROON = 'Maroon'
    MEDIUM_AQUAMARINE = 'MediumAquamarine'
    MEDIUM_BLUE = 'MediumBlue'
    MEDIUM_ORCHID = 'MediumOrchid'
    MEDIUM_PURPLE = 'MediumPurple'
    MEDIUM_SEA_GREEN = 'MediumSeaGreen'
    MEDIUM_SLATE_BLUE = 'MediumSlateBlue'
    MEDIUM_SPRING_GREEN = 'MediumSpringGreen'
    MEDIUM_TURQUOISE = 'MediumTurquoise'
    MEDIUM_VIOLET_RED = 'MediumVioletRed'
    MELON = 'Melon'
    MIDNIGHT_BLUE = 'MidnightBlue'
    MINT_CREAM = 'MintCream'
    MISTY_ROSE = 'MistyRose'
    MOCCASIN = 'Moccasin'
    MULBERRY = 'Mulberry'
    NAVAJO_WHITE = 'NavajoWhite'
    NAVY = 'Navy'
    NAVY_BLUE = 'NavyBlue'
    OLD_LACE = 'OldLace'
    OLIVE = 'olive'
    OLIVE_DRAB = 'OliveDrab'
    OLIVE_GREEN = 'OliveGreen'
    ORANGE = 'orange'
    ORANGE_RED = 'OrangeRed'
    ORCHID = 'Orchid'
    PALE_GOLDENROD = 'PaleGoldenrod'
    PALE_GREEN = 'PaleGreen'
    PALE_TURQUOISE = 'PaleTurquoise'
    PALE_VIOLET_RED = 'PaleVioletRed'
    PAPAYA_WHIP = 'PapayaWhip'
    PEACH = 'Peach'
    PEACH_PUFF = 'PeachPuff'
    PERIWINKLE = 'Periwinkle'
    PERU = 'Peru'
    PINE_GREEN = 'PineGreen'
    PINK = 'pink'
    PLUM = 'Plum'
    POWDER_BLUE = 'PowderBlue'
    PROCESS_BLUE = 'ProcessBlue'
    PURPLE = 'purple'
    RAW_SIENNA = 'RawSienna'
    RED = 'red'
    RED_ORANGE = 'RedOrange'
    RED_VIOLET = 'RedViolet'
    RHODAMINE = 'Rhodamine'
    ROSY_BROWN = 'RosyBrown'
    ROYAL_BLUE = 'RoyalBlue'
    ROYAL_PURPLE = 'RoyalPurple'
    RUBINE_RED = 'RubineRed'
    SADDLE_BROWN = 'SaddleBrown'
    SALMON = 'Salmon'
    SANDY_BROWN = 'SandyBrown'
    SEASHELL = 'Seashell'
    SEA_GREEN = 'SeaGreen'
    SEPIA = 'Sepia'
    SIENNA = 'Sienna'
    SILVER = 'Silver'
    SKY_BLUE = 'SkyBlue'
    SLATE_BLUE = 'SlateBlue'
    SLATE_GRAY = 'SlateGray'
    SLATE_GREY = 'SlateGrey'
    SNOW = 'Snow'
    SPRING_GREEN = 'SpringGreen'
    STEEL_BLUE = 'SteelBlue'
    TAN = 'Tan'
    TEAL = 'teal'
    TEAL_BLUE = 'TealBlue'
    THISTLE = 'Thistle'
    TOMATO = 'Tomato'
    TURQUOISE = 'Turquoise'
    VIOLET = 'violet'
    VIOLET_RED = 'VioletRed'
    WHEAT = 'Wheat'
    WHITE = 'white'
    WHITE_SMOKE = 'WhiteSmoke'
    WILD_STRAWBERRY = 'WildStrawberry'
    YELLOW = 'yellow'
    YELLOW_GREEN = 'YellowGreen'
    YELLOW_ORANGE = 'YellowOrange'

    @property
    def ansi_code(self) -> str:
        return f'\x1b[38;5;{_ansi_index[self]}m'

    @staticmethod
    def reset_code() -> str:
        return '\x1b[0m'

    def set(self, *, file: IO[str] = sys.stdout) -> None:
        print(self.ansi_code, end='', file=file, flush=True)

    @staticmethod
    def reset(*, file: IO[str] = sys.stdout) -> None:
        print(Color.reset_code(), end='', file=file, flush=True)


_ansi_index: Final = {
    Color.ALICE_BLUE: 231,
    Color.ANTIQUE_WHITE: 231,
    Color.APRICOT: 216,
    Color.AQUA: 51,
    Color.AQUAMARINE: 122,
    Color.AZURE: 231,
    Color.BEIGE: 230,
    Color.BISQUE: 223,
    Color.BITTERSWEET: 130,
    Color.BLACK: 16,
    Color.BLANCHED_ALMOND: 223,
    Color.BLUE: 21,
    Color.BLUE_GREEN: 37,
    Color.BLUE_VIOLET: 93,
    Color.BRICK_RED: 124,
    Color.BROWN: 137,
    Color.BURLY_WOOD: 180,
    Color.BURNT_ORANGE: 208,
    Color.CADET_BLUE: 73,
    Color.CARNATION_PINK: 211,
    Color.CERULEAN: 39,
    Color.CHARTREUSE: 118,
    Color.CHOCOLATE: 166,
    Color.CORAL: 209,
    Color.CORNFLOWER_BLUE: 68,
    Color.CORNSILK: 230,
    Color.CRIMSON: 197,
    Color.CYAN: 51,
    Color.DANDELION: 214,
    Color.DARKGRAY: 59,
    Color.DARK_BLUE: 18,
    Color.DARK_CYAN: 30,
    Color.DARK_GOLDENROD: 136,
    Color.DARK_GRAY: 145,
    Color.DARK_GREEN: 22,
    Color.DARK_GREY: 145,
    Color.DARK_KHAKI: 143,
    Color.DARK_MAGENTA: 90,
    Color.DARK_OLIVE_GREEN: 58,
    Color.DARK_ORANGE: 208,
    Color.DARK_ORCHID: 128,
    Color.DARK_RED: 88,
    Color.DARK_SALMON: 173,
    Color.DARK_SEA_GREEN: 108,
    Color.DARK_SLATE_BLUE: 61,
    Color.DARK_SLATE_GRAY: 23,
    Color.DARK_SLATE_GREY: 23,
    Color.DARK_TURQUOISE: 44,
    Color.DARK_VIOLET: 92,
    Color.DEEP_PINK: 198,
    Color.DEEP_SKY_BLUE: 74,
    Color.DIM_GRAY: 59,
    Color.DIM_GREY: 59,
    Color.DODGER_BLUE: 33,
    Color.EMERALD: 37,
    Color.FIRE_BRICK: 124,
    Color.FLORAL_WHITE: 231,
    Color.FOREST_GREEN: 28,
    Color.FUCHSIA: 201,
    Color.GAINSBORO: 188,
    Color.GHOST_WHITE: 231,
    Color.GOLD: 220,
    Color.GOLDENROD: 178,
    Color.GRAY: 102,
    Color.GREEN: 46,
    Color.GREEN_YELLOW: 154,
    Color.GREY: 102,
    Color.HONEYDEW: 231,
    Color.HOT_PINK: 205,
    Color.INDIAN_RED: 167,
    Color.INDIGO: 54,
    Color.IVORY: 231,
    Color.JUNGLE_GREEN: 37,
    Color.KHAKI: 186,
    Color.LAVENDER: 189,
    Color.LAVENDER_BLUSH: 231,
    Color.LAWN_GREEN: 118,
    Color.LEMON_CHIFFON: 230,
    Color.LIGHTGRAY: 145,
    Color.LIGHT_BLUE: 152,
    Color.LIGHT_CORAL: 210,
    Color.LIGHT_CYAN: 195,
    Color.LIGHT_GOLDENROD: 186,
    Color.LIGHT_GOLDENROD_YELLOW: 230,
    Color.LIGHT_GRAY: 188,
    Color.LIGHT_GREEN: 120,
    Color.LIGHT_GREY: 188,
    Color.LIGHT_PINK: 217,
    Color.LIGHT_SALMON: 216,
    Color.LIGHT_SEA_GREEN: 37,
    Color.LIGHT_SKY_BLUE: 117,
    Color.LIGHT_SLATE_BLUE: 99,
    Color.LIGHT_SLATE_GRAY: 102,
    Color.LIGHT_SLATE_GREY: 102,
    Color.LIGHT_STEEL_BLUE: 153,
    Color.LIGHT_YELLOW: 230,
    Color.LIME: 154,
    Color.LIME_GREEN: 40,
    Color.LINEN: 231,
    Color.MAGENTA: 201,
    Color.MAHOGANY: 124,
    Color.MAROON: 88,
    Color.MEDIUM_AQUAMARINE: 79,
    Color.MEDIUM_BLUE: 20,
    Color.MEDIUM_ORCHID: 134,
    Color.MEDIUM_PURPLE: 98,
    Color.MEDIUM_SEA_GREEN: 35,
    Color.MEDIUM_SLATE_BLUE: 99,
    Color.MEDIUM_SPRING_GREEN: 49,
    Color.MEDIUM_TURQUOISE: 44,
    Color.MEDIUM_VIOLET_RED: 162,
    Color.MELON: 216,
    Color.MIDNIGHT_BLUE: 18,
    Color.MINT_CREAM: 231,
    Color.MISTY_ROSE: 224,
    Color.MOCCASIN: 223,
    Color.MULBERRY: 126,
    Color.NAVAJO_WHITE: 223,
    Color.NAVY: 18,
    Color.NAVY_BLUE: 18,
    Color.OLD_LACE: 231,
    Color.OLIVE: 100,
    Color.OLIVE_DRAB: 64,
    Color.OLIVE_GREEN: 28,
    Color.ORANGE: 220,
    Color.ORANGE_RED: 202,
    Color.ORCHID: 170,
    Color.PALE_GOLDENROD: 187,
    Color.PALE_GREEN: 120,
    Color.PALE_TURQUOISE: 159,
    Color.PALE_VIOLET_RED: 168,
    Color.PAPAYA_WHIP: 230,
    Color.PEACH: 209,
    Color.PEACH_PUFF: 223,
    Color.PERIWINKLE: 104,
    Color.PERU: 173,
    Color.PINE_GREEN: 29,
    Color.PINK: 217,
    Color.PLUM: 182,
    Color.POWDER_BLUE: 152,
    Color.PROCESS_BLUE: 39,
    Color.PURPLE: 161,
    Color.RAW_SIENNA: 124,
    Color.RED: 196,
    Color.RED_ORANGE: 202,
    Color.RED_VIOLET: 125,
    Color.RHODAMINE: 205,
    Color.ROSY_BROWN: 138,
    Color.ROYAL_BLUE: 62,
    Color.ROYAL_PURPLE: 61,
    Color.RUBINE_RED: 198,
    Color.SADDLE_BROWN: 94,
    Color.SALMON: 210,
    Color.SANDY_BROWN: 215,
    Color.SEASHELL: 231,
    Color.SEA_GREEN: 29,
    Color.SEPIA: 52,
    Color.SIENNA: 130,
    Color.SILVER: 145,
    Color.SKY_BLUE: 117,
    Color.SLATE_BLUE: 62,
    Color.SLATE_GRAY: 102,
    Color.SLATE_GREY: 102,
    Color.SNOW: 231,
    Color.SPRING_GREEN: 48,
    Color.STEEL_BLUE: 67,
    Color.TAN: 180,
    Color.TEAL: 30,
    Color.TEAL_BLUE: 37,
    Color.THISTLE: 182,
    Color.TOMATO: 203,
    Color.TURQUOISE: 80,
    Color.VIOLET: 90,
    Color.VIOLET_RED: 162,
    Color.WHEAT: 223,
    Color.WHITE: 231,
    Color.WHITE_SMOKE: 231,
    Color.WILD_STRAWBERRY: 197,
    Color.YELLOW: 226,
    Color.YELLOW_GREEN: 112,
    Color.YELLOW_ORANGE: 214,
}
