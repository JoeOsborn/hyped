# TODO: find format for sending links to interpreter. Links are
# currently read from JSON file, but not used.
from interpreter import TileMap

import json


def vglc_tilemap (tw, th, tiles, game_grammar, level_grammar):
    gramDict = get_grammar(game_grammar, level_grammar)
    initTileArray = get_tiles(tiles)
    charOrder = []
    finalGram = []
    # print (gramDict["tiles"])

    gramString = ""
    i = 0
    if "-" in gramDict["tiles"]:
        charOrder.append("-")
        finalGram.append(set(gramDict["tiles"]["-"]))
    for char in gramDict["tiles"]:
        if char is "-":
            continue
        charOrder.append(char)
        finalGram.append(set(gramDict["tiles"][char]))
        gramString = gramString + char + ", " + str(i) + ": " + "".join(gramDict["tiles"][char]) + " "
        i = i + 1
    #print(finalGram[0])
    linkString = ""
    i = 0
    for link in gramDict["links"]:
        linkString = linkString + link + ": " + "".join(gramDict["links"][link])
        i = i + 1

    outputFile = open("tile_array1.txt", "w")
    outputFile.write(gramString)
    outputFile.write("\n\n")
    outputFile.write(linkString)
    outputFile.write("\n\n")

    finalTileArray = []

    for line in initTileArray:
        row = []
        for char in line:
            row.append(charOrder.index(char))
        outputFile.write("".join(line))
        outputFile.write("\n")
        finalTileArray.append(row)

    outputFile.write("\n\n")

    for line in finalTileArray:
        outputFile.write("".join(str(e) for e in line))
        outputFile.write("\n")

    outputFile.write("\n\n")

    outputFile.close()

    return TileMap(tw, th, finalGram, finalTileArray)


def get_tiles(tiles):
    tile_array = []
    vglc = open(tiles, "r")
    for line in vglc:
        tile_row = []
        for char in line:
            if char == "\n":
                continue
            tile_row.append(char)
        tile_array.append(tile_row)
    return tile_array


def get_grammar(game_grammar, level_grammar):
    with open(game_grammar, 'r') as myfile:
        game_gram_string = myfile.read()
    game_gram_dict = json.loads(game_gram_string)

    with open(level_grammar, 'r') as myfile:
        level_gram_string = myfile.read()
    level_gram_dict = json.loads(level_gram_string)

    for section in level_gram_dict:
        if section in game_gram_dict:
            game_gram_dict[section].update(level_gram_dict[section])
        else:
            game_gram_dict[section] = level_gram_dict[section]

    return game_gram_dict
