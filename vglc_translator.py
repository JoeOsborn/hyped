import interpreter
import json

def vglc_tilemap (tw, th, tiles, grammar):
    gramDict = get_grammar(grammar)
    initTileArray = get_tiles(tiles)
    charOrder = []
    finalGram = []
    print (gramDict["tiles"])
    for char in gramDict["tiles"]:
        charOrder.append(char)
        finalGram.append(set(gramDict["tiles"][char]))
    finalTileArray = []

    outputFile = open("tileArray.txt", "w")
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

    return (interpreter.TileMap(tw, th, finalGram, finalTileArray))

def get_tiles(tiles):
    tile_array = []
    vglc = open(tiles, "r")
    for line in vglc:
        tile_row = [];
        for char in line:
            if char == "\n":
                continue
            tile_row.append(char)
        tile_array.append(tile_row)
    return (tile_array)

def get_grammar(grammar):
    with open(grammar, 'r') as myfile:
        gramString = myfile.read()
    gramDict = json.loads(gramString)
    return(gramDict)

vglc_tilemap (16, 16, "resources/VGLC/mario_1_1.txt", "resources/VGLC/smb.json")
