namespace GolfWindowArtifact
open GolfLayout

def maskSites (sites : List Site) := sites.filter windowShape
def inRanges (sites : List Site) (pc : Nat) : Bool :=
 sites.any (fun site => site.pc ≤ pc && pc < site.pc+site.before.length)
def exteriorFactored (sites : List Site) (rows : List Row) :=
 rows.filter (fun row => !inRanges (maskSites sites) row.1)
def noInteriorFactored (sites : List Site) (rows : List Row) : Bool :=
 rows.all (fun row => !row.2.2 || (maskSites sites).all (fun site => !interior site row.1))

theorem inRanges_eq (sites : List Site) (pc : Nat) :
 inRanges (maskSites sites) pc = inMask sites pc := by
 simp only [inRanges,maskSites,List.any_filter,inMask,Bool.and_assoc]

theorem exteriorFactored_eq (sites : List Site) (rows : List Row) :
 exteriorFactored sites rows = exterior sites rows := by
 simp only [exteriorFactored,exterior,inRanges_eq]

theorem noInteriorFactored_eq (sites : List Site) (rows : List Row) :
 noInteriorFactored sites rows = noInteriorJump sites rows := by
 simp only [noInteriorFactored,noInteriorJump,maskSites,List.all_filter]
end GolfWindowArtifact
