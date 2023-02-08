#include "Game.h"
#include "Protocol.h"
#include "Block.h"
#include "Options.h"
#include "Inventory.h"

static const cc_uint8 v7_inventory[] = {
	BLOCK_STONE, BLOCK_COBBLE, BLOCK_BRICK, BLOCK_DIRT, BLOCK_WOOD, BLOCK_LOG, BLOCK_LEAVES, BLOCK_GLASS, BLOCK_SLAB,
	BLOCK_MOSSY_ROCKS, BLOCK_SAPLING, BLOCK_DANDELION, BLOCK_ROSE, BLOCK_BROWN_SHROOM, BLOCK_RED_SHROOM, BLOCK_SAND, BLOCK_GRAVEL, BLOCK_SPONGE,
	BLOCK_RED, BLOCK_ORANGE, BLOCK_YELLOW, BLOCK_LIME, BLOCK_GREEN, BLOCK_TEAL, BLOCK_AQUA, BLOCK_CYAN, BLOCK_BLUE,
	BLOCK_INDIGO, BLOCK_VIOLET, BLOCK_MAGENTA, BLOCK_PINK, BLOCK_BLACK, BLOCK_GRAY, BLOCK_WHITE, BLOCK_COAL_ORE, BLOCK_IRON_ORE,
	BLOCK_GOLD_ORE, BLOCK_IRON, BLOCK_GOLD, BLOCK_BOOKSHELF, BLOCK_TNT, BLOCK_OBSIDIAN,
};

static const cc_uint8 v7_hotbar[INVENTORY_BLOCKS_PER_HOTBAR] = {
	BLOCK_STONE, BLOCK_COBBLE, BLOCK_BRICK, BLOCK_DIRT, BLOCK_WOOD, BLOCK_LOG, BLOCK_LEAVES, BLOCK_GLASS, BLOCK_SLAB
};

static const struct GameVersion version_cpe  = { 
	"0.30", VERSION_CPE, 
	PROTOCOL_0030, BLOCK_MAX_CPE, 
	10, sizeof(v7_inventory), NULL,         v7_hotbar
};

void GameVersion_Load(void) {
	int version = Options_GetInt(OPT_GAME_VERSION, VERSION_CPE, VERSION_CPE, VERSION_CPE);
	const struct GameVersion* ver = &version_cpe;
	Game_Version = *ver;
}