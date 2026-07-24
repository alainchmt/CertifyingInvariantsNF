
import IdealArithmetic.Examples.NF3_1_856596_2.RI3_1_856596_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![6974932659272, 765393550221, 533832403404]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![6974932659272, 765393550221, 533832403404]] 
 ![![2, 0, 0], ![0, 1, 0], ![1, 0, 1]] where
  M :=![![![6974932659272, 765393550221, 533832403404], ![99080696703834, 10872610520147, 7583225392440], ![89031239292969, 9769834298319, 6814081622225]]]
  hmulB := by decide  
  f := ![![![-1841285, -183849, 348852]], ![![30321855, -673138, -1626372]], ![![-32366341, 2074266, 227261]]]
  g := ![![![3220550127934, 765393550221, 533832403404], ![45748735655697, 10872610520147, 7583225392440], ![41108578835372, 9769834298319, 6814081622225]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-270189307075480925936418711118, -29649197071364831812998714093, -20679168418698367726376276893]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![-270189307075480925936418711118, -29649197071364831812998714093, -20679168418698367726376276893]] 
 ![![2, 0, 0], ![1, 1, 0], ![1, 0, 1]] where
  M :=![![![-270189307075480925936418711118, -29649197071364831812998714093, -20679168418698367726376276893], ![-3838107992537800078446593294619, -421174403545670524554543684076, -293752859600282878576855738437], ![-3448820229204817238706036304770, -378455949075871643608264018781, -263958389536179901402927676411]]]
  hmulB := by decide  
  f := ![![![-505567349945939, -27493198967210, 70203937163227]], ![![5877785167070990, -202464167162549, -235163130966487]], ![![-5739803050171429, 436441162208169, -36034033614087]]]
  g := ![![![-109930470792708863198521860066, -29649197071364831812998714093, -20679168418698367726376276893], ![-1561590364695923337657596936053, -421174403545670524554543684076, -293752859600282878576855738437], ![-1403202945296382846847422304789, -378455949075871643608264018781, -263958389536179901402927676411]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N1 : Nat.card (O ⧸ I2N1) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N1)

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := prime_ideal_of_norm_prime hp2.out _ NI2N1
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![6974932659272, 765393550221, 533832403404]] ![![-270189307075480925936418711118, -29649197071364831812998714093, -20679168418698367726376276893]]
  ![![-6663307316511687095866402317659508047183975, -731197373844001586076307006639004201831616, -509981892751945002123245135991512422249517]] where
 M := ![![![-6663307316511687095866402317659508047183975, -731197373844001586076307006639004201831616, -509981892751945002123245135991512422249517]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI2N1 : IdealMulLeCertificate' Table 
  ![![-6663307316511687095866402317659508047183975, -731197373844001586076307006639004201831616, -509981892751945002123245135991512422249517]] ![![-270189307075480925936418711118, -29649197071364831812998714093, -20679168418698367726376276893]]
  ![![2, 0, 0]] where
 M := ![![![6365604739603656739157225373916028281692968502501501613712902736238104444, 698529010810176938941887275473418138325367384256209014535520459204985268, 487196972825999019140951367821234803600188149450595225521521551602457354]]]
 hmul := by decide  
 g := ![![![![3182802369801828369578612686958014140846484251250750806856451368119052222, 349264505405088469470943637736709069162683692128104507267760229602492634, 243598486412999509570475683910617401800094074725297612760760775801228677]]]]
 hle2 := by decide  


def PBC2 : ContainsPrimesAboveP 2 ![I2N0, I2N1, I2N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI2N0
    exact isPrimeI2N1
    exact isPrimeI2N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 2 (by decide) (𝕀 ⊙ MulI2N0 ⊙ MulI2N1)

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0], ![-1, 0, 1]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![3, 0, 0], ![-1, 0, 1]] 
 ![![3, 0, 0], ![0, 1, 0], ![2, 0, 1]] where
  M :=![![![3, 0, 0], ![0, 3, 0], ![0, 0, 3]], ![![-1, 0, 1], ![177, 2, -3], ![-87, 14, 3]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![-107, -1, -9], ![33, 2, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 3, 0], ![-2, 0, 3]], ![![-1, 0, 1], ![61, 2, -3], ![-31, 14, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N0 : Nat.card (O ⧸ I3N0) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N0)

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := prime_ideal_of_norm_prime hp3.out _ NI3N0

def I3N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0], ![-3, 0, 1]] i)))

def SI3N1: IdealEqSpanCertificate' Table ![![3, 0, 0], ![-3, 0, 1]] 
 ![![3, 0, 0], ![0, 1, 0], ![0, 0, 1]] where
  M :=![![![3, 0, 0], ![0, 3, 0], ![0, 0, 3]], ![![-3, 0, 1], ![177, 0, -3], ![-87, 14, 1]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![-13, 5, -5], ![16, 0, -1]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 3, 0], ![0, 0, 3]], ![![-1, 0, 1], ![59, 0, -3], ![-29, 14, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N1 : Nat.card (O ⧸ I3N1) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N1)

lemma isPrimeI3N1 : Ideal.IsPrime I3N1 := prime_ideal_of_norm_prime hp3.out _ NI3N1
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![3, 0, 0], ![-1, 0, 1]] ![![3, 0, 0], ![-3, 0, 1]]
  ![![3, 0, 0], ![0, 1, 0]] where
 M := ![![![9, 0, 0], ![-9, 0, 3]], ![![-3, 0, 3], ![-84, 14, 0]]]
 hmul := by decide  
 g := ![![![![3, 0, 0], ![0, 0, 0]], ![![-3, 0, 1], ![0, 0, 0]]], ![![![-1, 0, 1], ![0, 0, 0]], ![![-28, 4, 0], ![2, 0, 0]]]]
 hle2 := by decide  

def MulI3N1 : IdealMulLeCertificate' Table 
  ![![3, 0, 0], ![0, 1, 0]] ![![3, 0, 0], ![-3, 0, 1]]
  ![![3, 0, 0]] where
 M := ![![![9, 0, 0], ![-9, 0, 3]], ![![0, 3, 0], ![177, 0, -3]]]
 hmul := by decide  
 g := ![![![![3, 0, 0]], ![![-3, 0, 1]]], ![![![0, 1, 0]], ![![59, 0, -1]]]]
 hle2 := by decide  


def PBC3 : ContainsPrimesAboveP 3 ![I3N0, I3N1, I3N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI3N0
    exact isPrimeI3N1
    exact isPrimeI3N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 3 (by decide) (𝕀 ⊙ MulI3N0 ⊙ MulI3N1)
instance hp5 : Fact (Nat.Prime 5) := {out := by norm_num}

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0, 0]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![5, 0, 0]] 
 ![![5, 0, 0], ![0, 5, 0], ![0, 0, 5]] where
  M :=![![![5, 0, 0], ![0, 5, 0], ![0, 0, 5]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P5P0 : CertificateIrreducibleZModOfList' 5 3 2 2 [3, 1, 1, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 3, 3], [4, 1, 2], [0, 1]]
 g := ![![[0, 4, 1], []], ![[2, 3, 4, 3], [4, 4]], ![[3, 0, 3, 3], [0, 4]]]
 h' := ![![[0, 3, 3], [0, 0, 1], [0, 1]], ![[4, 1, 2], [3, 4, 1], [0, 3, 3]], ![[0, 1], [1, 1, 3], [4, 1, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2, 4], []]
 b := ![[], [3, 0, 2], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI5N0 : CertifiedPrimeIdeal' SI5N0 5 where
  n := 3
  hpos := by decide
  P := [3, 1, 1, 1]
  hirr := P5P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-620490, -31940, -13620]
  a := ![-3, -2, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-124098, -6388, -2724]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI5N0 B_one_repr
lemma NI5N0 : Nat.card (O ⧸ I5N0) = 125 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI5N0

def PBC5 : ContainsPrimesAboveP 5 ![I5N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI5N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![5, 0, 0]]) timesTableT_eq_Table B_one_repr 5 (by decide) 𝕀

instance hp7 : Fact (Nat.Prime 7) := {out := by norm_num}

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1766105217606617950, -193803382570413222, -135170364939077319]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![-1766105217606617950, -193803382570413222, -135170364939077319]] 
 ![![7, 0, 0], ![0, 1, 0], ![4, 0, 1]] where
  M :=![![![-1766105217606617950, -193803382570413222, -135170364939077319], ![-25087974889639164795, -2753026460135089573, -1920129496027726707], ![-22543376965263413541, -2473795256858322132, -1725376529651687560]]]
  hmulB := by decide  
  f := ![![![-944232556, 279994212, -237625167]], ![![-5768527041, -116732203, 581829435]], ![![9493633547, -195256122, -526459504]]]
  g := ![![![-175060536835758382, -193803382570413222, -135170364939077319], ![-2486779557932608281, -2753026460135089573, -1920129496027726707], ![-2234552978093809043, -2473795256858322132, -1725376529651687560]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N0 : Nat.card (O ⧸ I7N0) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N0)

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := prime_ideal_of_norm_prime hp7.out _ NI7N0

def I7N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0], ![3, 1, 0]] i)))

def SI7N1: IdealEqSpanCertificate' Table ![![7, 0, 0], ![3, 1, 0]] 
 ![![7, 0, 0], ![3, 1, 0], ![6, 0, 1]] where
  M :=![![![7, 0, 0], ![0, 7, 0], ![0, 0, 7]], ![![3, 1, 0], ![6, 6, 12], ![177, 3, 0]]]
  hmulB := by decide  
  f := ![![![46, 55, 120], ![35, -70, 0]], ![![18, 22, 48], ![15, -28, 0]], ![![39, 47, 103], ![31, -60, 0]]]
  g := ![![![1, 0, 0], ![-3, 7, 0], ![-6, 0, 7]], ![![0, 1, 0], ![-12, 6, 12], ![24, 3, 0]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N1 : Nat.card (O ⧸ I7N1) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N1)

lemma isPrimeI7N1 : Ideal.IsPrime I7N1 := prime_ideal_of_norm_prime hp7.out _ NI7N1

def I7N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0], ![-3, 1, 0]] i)))

def SI7N2: IdealEqSpanCertificate' Table ![![7, 0, 0], ![-3, 1, 0]] 
 ![![7, 0, 0], ![4, 1, 0], ![4, 0, 1]] where
  M :=![![![7, 0, 0], ![0, 7, 0], ![0, 0, 7]], ![![-3, 1, 0], ![6, 0, 12], ![177, 3, -6]]]
  hmulB := by decide  
  f := ![![![43, 2, 96], ![-14, -56, 0]], ![![22, 1, 48], ![-6, -28, 0]], ![![25, 1, 55], ![-7, -32, 0]]]
  g := ![![![1, 0, 0], ![-4, 7, 0], ![-4, 0, 7]], ![![-1, 1, 0], ![-6, 0, 12], ![27, 3, -6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N2 : Nat.card (O ⧸ I7N2) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N2)

lemma isPrimeI7N2 : Ideal.IsPrime I7N2 := prime_ideal_of_norm_prime hp7.out _ NI7N2
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![-1766105217606617950, -193803382570413222, -135170364939077319]] ![![7, 0, 0], ![3, 1, 0]]
  ![![7, 0, 0], ![-3, -3, 1]] where
 M := ![![![-12362736523246325650, -1356623677992892554, -946192554573541233], ![-30386290542459018645, -3334436607846329239, -2325640590844958664]]]
 hmul := by decide  
 g := ![![![![-1512668948389323115, 59632886646881613, -219649121344842264], ![591351294840354615, 0, 0]], ![![-3717979273754201706, 146571288333325352, -539874161843546795], ![1453478542059868901, 0, 0]]]]
 hle2 := by decide  

def MulI7N1 : IdealMulLeCertificate' Table 
  ![![7, 0, 0], ![-3, -3, 1]] ![![7, 0, 0], ![-3, 1, 0]]
  ![![7, 0, 0]] where
 M := ![![![49, 0, 0], ![-21, 7, 0]], ![![-21, -21, 7], ![168, 0, -42]]]
 hmul := by decide  
 g := ![![![![7, 0, 0]], ![![-3, 1, 0]]], ![![![-3, -3, 1]], ![![24, 0, -6]]]]
 hle2 := by decide  


def PBC7 : ContainsPrimesAboveP 7 ![I7N0, I7N1, I7N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI7N0
    exact isPrimeI7N1
    exact isPrimeI7N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 7 (by decide) (𝕀 ⊙ MulI7N0 ⊙ MulI7N1)
instance hp11 : Fact (Nat.Prime 11) := {out := by norm_num}

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1365420617645065377648931, 149834297352683911694626, 104503628290358006492994]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![1365420617645065377648931, 149834297352683911694626, 104503628290358006492994]] 
 ![![11, 0, 0], ![0, 11, 0], ![4, 10, 1]] where
  M :=![![![1365420617645065377648931, 149834297352683911694626, 104503628290358006492994], ![19396147991509470619427694, 2128434394574191132211791, 1484500683361132920856530], ![17428854970163905805058324, 1912553688123063825985794, 1333932238748445668537029]]]
  hmulB := by decide  
  f := ![![![-236194384171, 91016656462, -82786153134]], ![![-14107049165946, -211502874187, 1340558336946]], ![![-10791175061792, -239719844592, 1112186344621]]]
  g := ![![![86127827680330304697905, -81381998686445104839574, 104503628290358006492994], ![1223467750733176266909234, -1156052039912467097850319, 1484500683361132920856530], ![1099375092288193011900928, -1038797154487399350853136, 1333932238748445668537029]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P0 : CertificateIrreducibleZModOfList' 11 2 2 3 [2, 5, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [6, 10], [0, 1]]
 g := ![![[8, 3], [5, 3], [1]], ![[4, 8], [1, 8], [1]]]
 h' := ![![[6, 10], [1, 6], [9, 6], [0, 1]], ![[0, 1], [4, 5], [1, 5], [6, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3]]
 b := ![[], [1, 7]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 2
  hpos := by decide
  P := [2, 5, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2159, 350, 145]
  a := ![2, 0, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-249, -100, 145]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N0 B_one_repr
lemma NI11N0 : Nat.card (O ⧸ I11N0) = 121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N0

def I11N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![236194384171, -91016656462, 82786153134]] i)))

def SI11N1: IdealEqSpanCertificate' Table ![![236194384171, -91016656462, 82786153134]] 
 ![![11, 0, 0], ![4, 1, 0], ![0, 0, 1]] where
  M :=![![![236194384171, -91016656462, 82786153134], ![14107049165946, 211502874187, -1340558336946], ![-23312343516432, 885956174490, 840388966093]]]
  hmulB := by decide  
  f := ![![![-1365420617645065377648931, -149834297352683911694626, -104503628290358006492994]], ![![-2259802769280884739093038, -247979234907720616271845, -172955926956596813348046]], ![![-1584441360923991436823484, -173868517102096711453254, -121266567158949606230639]]]
  g := ![![![54569182729, -91016656462, 82786153134], ![1205548879018, 211502874187, -1340558336946], ![-2441469837672, 885956174490, 840388966093]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N1 : Nat.card (O ⧸ I11N1) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N1)

lemma isPrimeI11N1 : Ideal.IsPrime I11N1 := prime_ideal_of_norm_prime hp11.out _ NI11N1
def MulI11N0 : IdealMulLeCertificate' Table 
  ![![1365420617645065377648931, 149834297352683911694626, 104503628290358006492994]] ![![236194384171, -91016656462, 82786153134]]
  ![![11, 0, 0]] where
 M := ![![![-11, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC11 : ContainsPrimesAboveP 11 ![I11N0, I11N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI11N0
    exact isPrimeI11N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 11 (by decide) (𝕀 ⊙ MulI11N0)

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0], ![4, 1, 0]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![13, 0, 0], ![4, 1, 0]] 
 ![![13, 0, 0], ![4, 1, 0], ![9, 0, 1]] where
  M :=![![![13, 0, 0], ![0, 13, 0], ![0, 0, 13]], ![![4, 1, 0], ![6, 7, 12], ![177, 3, 1]]]
  hmulB := by decide  
  f := ![![![637, 819, 1440], ![273, -1560, 0]], ![![192, 246, 432], ![79, -468, 0]], ![![441, 567, 997], ![189, -1080, 0]]]
  g := ![![![1, 0, 0], ![-4, 13, 0], ![-9, 0, 13]], ![![0, 1, 0], ![-10, 7, 12], ![12, 3, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N0 : Nat.card (O ⧸ I13N0) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N0)

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := prime_ideal_of_norm_prime hp13.out _ NI13N0

def I13N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0], ![-2, 1, 0]] i)))

def SI13N1: IdealEqSpanCertificate' Table ![![13, 0, 0], ![-2, 1, 0]] 
 ![![13, 0, 0], ![11, 1, 0], ![5, 0, 1]] where
  M :=![![![13, 0, 0], ![0, 13, 0], ![0, 0, 13]], ![![-2, 1, 0], ![6, 1, 12], ![177, 3, -5]]]
  hmulB := by decide  
  f := ![![![355, 63, 720], ![-39, -780, 0]], ![![295, 53, 600], ![-38, -650, 0]], ![![137, 24, 277], ![-12, -300, 0]]]
  g := ![![![1, 0, 0], ![-11, 13, 0], ![-5, 0, 13]], ![![-1, 1, 0], ![-5, 1, 12], ![13, 3, -5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N1 : Nat.card (O ⧸ I13N1) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N1)

lemma isPrimeI13N1 : Ideal.IsPrime I13N1 := prime_ideal_of_norm_prime hp13.out _ NI13N1
def MulI13N0 : IdealMulLeCertificate' Table 
  ![![13, 0, 0], ![4, 1, 0]] ![![13, 0, 0], ![-2, 1, 0]]
  ![![13, 0, 0], ![2, -5, 1]] where
 M := ![![![169, 0, 0], ![-26, 13, 0]], ![![52, 13, 0], ![-2, 5, 12]]]
 hmul := by decide  
 g := ![![![![11, 5, -1], ![13, 0, 0]], ![![-2, 1, 0], ![0, 0, 0]]], ![![![2, 6, -1], ![13, 0, 0]], ![![-2, 5, 0], ![12, 0, 0]]]]
 hle2 := by decide  

def MulI13N1 : IdealMulLeCertificate' Table 
  ![![13, 0, 0], ![2, -5, 1]] ![![13, 0, 0], ![-2, 1, 0]]
  ![![13, 0, 0]] where
 M := ![![![169, 0, 0], ![-26, 13, 0]], ![![26, -65, 13], ![143, 0, -65]]]
 hmul := by decide  
 g := ![![![![13, 0, 0]], ![![-2, 1, 0]]], ![![![2, -5, 1]], ![![11, 0, -5]]]]
 hle2 := by decide  


def PBC13 : ContainsPrimesAboveP 13 ![I13N0, I13N1, I13N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI13N0
    exact isPrimeI13N1
    exact isPrimeI13N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 13 (by decide) (𝕀 ⊙ MulI13N0 ⊙ MulI13N1)

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 0, 0], ![0, 1, 0]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![17, 0, 0], ![0, 1, 0]] 
 ![![17, 0, 0], ![0, 1, 0], ![9, 0, 1]] where
  M :=![![![17, 0, 0], ![0, 17, 0], ![0, 0, 17]], ![![0, 1, 0], ![6, 3, 12], ![177, 3, -3]]]
  hmulB := by decide  
  f := ![![![-17, -9, -36], ![0, 51, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![-9, -5, -19], ![4, 27, 0]]]
  g := ![![![1, 0, 0], ![0, 17, 0], ![-9, 0, 17]], ![![0, 1, 0], ![-6, 3, 12], ![12, 3, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N0 : Nat.card (O ⧸ I17N0) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N0)

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := prime_ideal_of_norm_prime hp17.out _ NI17N0
def MulI17N0 : IdealMulLeCertificate' Table 
  ![![17, 0, 0], ![0, 1, 0]] ![![17, 0, 0], ![0, 1, 0]]
  ![![17, 0, 0], ![-8, -4, 1]] where
 M := ![![![289, 0, 0], ![0, 17, 0]], ![![0, 17, 0], ![6, 3, 12]]]
 hmul := by decide  
 g := ![![![![17, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]]], ![![![0, 1, 0], ![0, 0, 0]], ![![6, 3, 0], ![12, 0, 0]]]]
 hle2 := by decide  
def MulI17N1 : IdealMulLeCertificate' Table 
  ![![17, 0, 0], ![-8, -4, 1]] ![![17, 0, 0], ![0, 1, 0]]
  ![![17, 0, 0]] where
 M := ![![![289, 0, 0], ![0, 17, 0]], ![![-136, -68, 17], ![153, -17, -51]]]
 hmul := by decide  
 g := ![![![![17, 0, 0]], ![![0, 1, 0]]], ![![![-8, -4, 1]], ![![9, -1, -3]]]]
 hle2 := by decide  

def PBC17 : ContainsPrimesAboveP 17 ![I17N0, I17N0, I17N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI17N0
    exact isPrimeI17N0
    exact isPrimeI17N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 17 (by decide) (𝕀 ⊙ MulI17N0 ⊙ MulI17N1)

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-119, -6, 16]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![-119, -6, 16]] 
 ![![19, 0, 0], ![6, 1, 0], ![15, 0, 1]] where
  M :=![![![-119, -6, 16], ![2796, -89, -120], ![-2454, 206, -37]]]
  hmulB := by decide  
  f := ![![![-28013, -3074, -2144]], ![![-29790, -3269, -2280]], ![![-40935, -4492, -3133]]]
  g := ![![![-17, -6, 16], ![270, -89, -120], ![-165, 206, -37]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N0 : Nat.card (O ⧸ I19N0) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N0)

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := prime_ideal_of_norm_prime hp19.out _ NI19N0

def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-146031643, -16024768, -11176656]] i)))

def SI19N1: IdealEqSpanCertificate' Table ![![-146031643, -16024768, -11176656]] 
 ![![19, 0, 0], ![7, 1, 0], ![1, 0, 1]] where
  M :=![![![-146031643, -16024768, -11176656], ![-2074416720, -227635915, -158767248], ![-1864014864, -204547488, -142663963]]]
  hmulB := by decide  
  f := ![![![41879, -4544, 1776]], ![![30539, 93, -2496]], ![![-48259, 352, 3389]]]
  g := ![![![-1193769, -16024768, -11176656], ![-16957793, -227635915, -158767248], ![-15237815, -204547488, -142663963]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N1 : Nat.card (O ⧸ I19N1) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N1)

lemma isPrimeI19N1 : Ideal.IsPrime I19N1 := prime_ideal_of_norm_prime hp19.out _ NI19N1
def MulI19N0 : IdealMulLeCertificate' Table 
  ![![-119, -6, 16]] ![![-119, -6, 16]]
  ![![-41879, 4544, -1776]] where
 M := ![![![-41879, 4544, -1776]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI19N1 : IdealMulLeCertificate' Table 
  ![![-41879, 4544, -1776]] ![![-146031643, -16024768, -11176656]]
  ![![19, 0, 0]] where
 M := ![![![-19, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC19 : ContainsPrimesAboveP 19 ![I19N0, I19N0, I19N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI19N0
    exact isPrimeI19N0
    exact isPrimeI19N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 19 (by decide) (𝕀 ⊙ MulI19N0 ⊙ MulI19N1)
instance hp23 : Fact (Nat.Prime 23) := {out := by norm_num}

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 0, 0]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![23, 0, 0]] 
 ![![23, 0, 0], ![0, 23, 0], ![0, 0, 23]] where
  M :=![![![23, 0, 0], ![0, 23, 0], ![0, 0, 23]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P0 : CertificateIrreducibleZModOfList' 23 3 2 4 [8, 2, 20, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [1, 18, 3], [2, 4, 20], [0, 1]]
 g := ![![[20, 3, 9], [5, 6, 3], [7, 3, 1], []], ![[2, 3], [17, 4, 22, 16], [22, 14, 11, 2], [20, 9]], ![[18, 0, 22, 19], [6, 4, 22, 22], [19, 3, 16, 17], [3, 9]]]
 h' := ![![[1, 18, 3], [6, 19, 3], [13, 8, 7], [0, 0, 1], [0, 1]], ![[2, 4, 20], [8, 22], [12, 3, 6], [2, 16, 4], [1, 18, 3]], ![[0, 1], [7, 5, 20], [4, 12, 10], [3, 7, 18], [2, 4, 20]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [0, 9], []]
 b := ![[], [1, 3, 20], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 3
  hpos := by decide
  P := [8, 2, 20, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-21035830291, -1140477080, -464124130]
  a := ![-129, -64, -194]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-914601317, -49585960, -20179310]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N0 B_one_repr
lemma NI23N0 : Nat.card (O ⧸ I23N0) = 12167 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N0

def PBC23 : ContainsPrimesAboveP 23 ![I23N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI23N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![23, 0, 0]]) timesTableT_eq_Table B_one_repr 23 (by decide) 𝕀

instance hp29 : Fact (Nat.Prime 29) := {out := by norm_num}

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, 0, 0]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![29, 0, 0]] 
 ![![29, 0, 0], ![0, 29, 0], ![0, 0, 29]] where
  M :=![![![29, 0, 0], ![0, 29, 0], ![0, 0, 29]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P0 : CertificateIrreducibleZModOfList' 29 3 2 4 [27, 13, 0, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [21, 27, 8], [8, 1, 21], [0, 1]]
 g := ![![[25, 19, 9], [16, 7], [24], [1]], ![[26, 28, 11, 10], [23, 20], [3, 3, 6, 21], [19, 24, 22, 19]], ![[25, 18, 11, 8], [18, 24], [18, 28, 26, 8], [12, 19, 18, 10]]]
 h' := ![![[21, 27, 8], [16, 21, 26], [19, 11, 6], [2, 16], [0, 1]], ![[8, 1, 21], [22, 28, 20], [18, 12, 7], [19, 26, 12], [21, 27, 8]], ![[0, 1], [1, 9, 12], [9, 6, 16], [14, 16, 17], [8, 1, 21]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [19, 21], []]
 b := ![[], [6, 27, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 3
  hpos := by decide
  P := [27, 13, 0, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-822411, -39150, 13108]
  a := ![-3, -1, -7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-28359, -1350, 452]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N0 B_one_repr
lemma NI29N0 : Nat.card (O ⧸ I29N0) = 24389 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N0

def PBC29 : ContainsPrimesAboveP 29 ![I29N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI29N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![29, 0, 0]]) timesTableT_eq_Table B_one_repr 29 (by decide) 𝕀

instance hp31 : Fact (Nat.Prime 31) := {out := by norm_num}

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0], ![7, -7, 1]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![31, 0, 0], ![7, -7, 1]] 
 ![![31, 0, 0], ![0, 31, 0], ![7, 24, 1]] where
  M :=![![![31, 0, 0], ![0, 31, 0], ![0, 0, 31]], ![![7, -7, 1], ![135, -11, -87], ![-1326, -7, 32]]]
  hmulB := by decide  
  f := ![![![-6, 7, -1], ![31, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-7, -24, 31]], ![![0, -1, 1], ![24, 67, -87], ![-50, -25, 32]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P0 : CertificateIrreducibleZModOfList' 31 2 2 4 [13, 30, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [1, 30], [0, 1]]
 g := ![![[19, 18], [23, 18], [22, 20], [1, 1]], ![[6, 13], [10, 13], [11, 11], [2, 30]]]
 h' := ![![[1, 30], [11, 24], [24, 24], [18, 19], [0, 1]], ![[0, 1], [4, 7], [17, 7], [6, 12], [1, 30]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [25]]
 b := ![[], [17, 28]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 2
  hpos := by decide
  P := [13, 30, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1072, 540, -24]
  a := ![-3, -2, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![40, 36, -24]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N0 B_one_repr
lemma NI31N0 : Nat.card (O ⧸ I31N0) = 961 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N0

def I31N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0], ![-6, 1, 0]] i)))

def SI31N1: IdealEqSpanCertificate' Table ![![31, 0, 0], ![-6, 1, 0]] 
 ![![31, 0, 0], ![25, 1, 0], ![30, 0, 1]] where
  M :=![![![31, 0, 0], ![0, 31, 0], ![0, 0, 31]], ![![-6, 1, 0], ![6, -3, 12], ![177, 3, -9]]]
  hmulB := by decide  
  f := ![![![439, -223, 900], ![-62, -2325, 0]], ![![349, -178, 720], ![-61, -1860, 0]], ![![420, -215, 871], ![-85, -2250, 0]]]
  g := ![![![1, 0, 0], ![-25, 31, 0], ![-30, 0, 31]], ![![-1, 1, 0], ![-9, -3, 12], ![12, 3, -9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N1 : Nat.card (O ⧸ I31N1) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N1)

lemma isPrimeI31N1 : Ideal.IsPrime I31N1 := prime_ideal_of_norm_prime hp31.out _ NI31N1
def MulI31N0 : IdealMulLeCertificate' Table 
  ![![31, 0, 0], ![7, -7, 1]] ![![31, 0, 0], ![-6, 1, 0]]
  ![![31, 0, 0]] where
 M := ![![![961, 0, 0], ![-186, 31, 0]], ![![217, -217, 31], ![93, 31, -93]]]
 hmul := by decide  
 g := ![![![![31, 0, 0]], ![![-6, 1, 0]]], ![![![7, -7, 1]], ![![3, 1, -3]]]]
 hle2 := by decide  


def PBC31 : ContainsPrimesAboveP 31 ![I31N0, I31N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI31N0
    exact isPrimeI31N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 31 (by decide) (𝕀 ⊙ MulI31N0)


lemma PB262I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 31 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 31 (by omega)

def PB262I0 : PrimesBelowBoundCertificateInterval O 1 31 262 where
  m := 11
  g := ![3, 3, 1, 3, 2, 3, 3, 3, 1, 1, 2]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]
  hP := PB262I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N1, I2N1]
    · exact ![I3N0, I3N1, I3N1]
    · exact ![I5N0]
    · exact ![I7N0, I7N1, I7N2]
    · exact ![I11N0, I11N1]
    · exact ![I13N0, I13N1, I13N1]
    · exact ![I17N0, I17N0, I17N0]
    · exact ![I19N0, I19N0, I19N1]
    · exact ![I23N0]
    · exact ![I29N0]
    · exact ![I31N0, I31N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC2
    · exact PBC3
    · exact PBC5
    · exact PBC7
    · exact PBC11
    · exact PBC13
    · exact PBC17
    · exact PBC19
    · exact PBC23
    · exact PBC29
    · exact PBC31
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![2, 2, 2]
    · exact ![3, 3, 3]
    · exact ![125]
    · exact ![7, 7, 7]
    · exact ![121, 11]
    · exact ![13, 13, 13]
    · exact ![17, 17, 17]
    · exact ![19, 19, 19]
    · exact ![12167]
    · exact ![24389]
    · exact ![961, 31]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI2N0
      exact NI2N1
      exact NI2N1
    · dsimp ; intro j
      fin_cases j
      exact NI3N0
      exact NI3N1
      exact NI3N1
    · dsimp ; intro j
      fin_cases j
      exact NI5N0
    · dsimp ; intro j
      fin_cases j
      exact NI7N0
      exact NI7N1
      exact NI7N2
    · dsimp ; intro j
      fin_cases j
      exact NI11N0
      exact NI11N1
    · dsimp ; intro j
      fin_cases j
      exact NI13N0
      exact NI13N1
      exact NI13N1
    · dsimp ; intro j
      fin_cases j
      exact NI17N0
      exact NI17N0
      exact NI17N0
    · dsimp ; intro j
      fin_cases j
      exact NI19N0
      exact NI19N0
      exact NI19N1
    · dsimp ; intro j
      fin_cases j
      exact NI23N0
    · dsimp ; intro j
      fin_cases j
      exact NI29N0
    · dsimp ; intro j
      fin_cases j
      exact NI31N0
      exact NI31N1
  β := ![I2N0, I2N1, I3N0, I3N1, I5N0, I7N0, I7N1, I7N2, I11N0, I11N1, I13N0, I13N1, I17N0, I19N0, I19N1, I31N1]
  Il := ![[I2N0, I2N1, I2N1], [I3N0, I3N1, I3N1], [I5N0], [I7N0, I7N1, I7N2], [I11N0, I11N1], [I13N0, I13N1, I13N1], [I17N0, I17N0, I17N0], [I19N0, I19N0, I19N1], [], [], [I31N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
