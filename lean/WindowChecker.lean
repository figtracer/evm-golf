namespace GolfWindowArtifact
open GolfLayout

def oldProfile (site : Site) : Bool :=
 if site.requiredStack == 1 then
   profile site.before == some (1,0,1) && profile site.after == some (1,0,1)
 else site.requiredStack == 0 &&
   ((profile site.before == some (0,1,2) && profile site.after == some (0,1,2)) ||
    (profile site.before == some (0,2,2) && profile site.after == some (0,2,2)) || zeroChainProfile site)

def localSite (site : Site) : Site := ⟨0,site.before,site.after,site.requiredStack⟩

def checkOld (site : Site) : Bool :=
 decide (site.before.all (fun b => b<256) = true) &&
 decide (site.after.all (fun b => b<256) = true) &&
 decide (applySites site.before [localSite site] = some site.after) &&
 decide (site.before.length = site.after.length) &&
 decide (scan site.before = scan site.after) &&
 decide (aligned [localSite site] ((scan site.before).map (fun row => row.1) ++ [site.before.length]) = true) &&
 oldProfile (localSite site) && GolfReflected.checkSites [localSite site]

theorem checkOld_sound (site : Site) (h : checkOld site = true) :
 LayoutArtifact site.before site.after [localSite site] := by
 simp only [checkOld, Bool.and_eq_true, decide_eq_true_eq] at h
 rcases h with ⟨⟨⟨⟨⟨⟨⟨b,a⟩,r⟩,len⟩,scan⟩,align⟩,prof⟩,checkedLocal⟩
 refine ⟨b,a,r,len,scan,align,?_,GolfReflected.checkSites_sound _ checkedLocal⟩
 simpa only [List.all_cons, List.all_nil, Bool.and_true, oldProfile] using prof

theorem checkMask_sound (site : Site) (h : maskShape site = true) : MaskEquivalent site := by
 cases site with
 | mk pc before after required =>
   simp only [maskShape, Bool.and_eq_true, beq_iff_eq] at h
   rcases h with ⟨⟨requiredEq,beforeEq⟩,afterEq⟩
   subst required; subst before; subst after
   exact exact_mask pc

theorem checkIdempotent_sound (site : Site) (h : idempotentShape site = true) : IdempotentEquivalent site := by
 cases site with
 | mk pc before after required =>
   simp only [idempotentShape, Bool.and_eq_true, beq_iff_eq] at h
   rcases h with ⟨⟨requiredEq,beforeEq⟩,afterEq⟩
   subst required; subst before; subst after
   exact exact_idempotent pc

def checkSite (site : Site) : Bool := maskShape site || (idempotentShape site || checkOld site)
def checkSites (sites : List Site) : Bool := sites.all checkSite

theorem checkSites_sound (sites : List Site) (h : checkSites sites = true) :
 CertifiedWindowSites sites := by
 induction sites with
 | nil => exact .nil
 | cons site sites ih =>
   simp only [checkSites,List.all_cons,Bool.and_eq_true] at h
   have checked := h.1
   simp only [checkSite,Bool.or_eq_true] at checked
   rcases checked with mask | idempotent | old
   · exact .mask (checkMask_sound site mask) (ih h.2)
   · exact .idempotent (checkIdempotent_sound site idempotent) (ih h.2)
   · exact .old (checkOld_sound site old) (ih h.2)
end GolfWindowArtifact
