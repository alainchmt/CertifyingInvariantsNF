
import IdealArithmetic.Examples.NF3_1_482727_1.RI3_1_482727_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp2 : Fact (Nat.Prime 2) := {out := by norm_num}

def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![2, 0, 0]] 
 ![![2, 0, 0], ![0, 2, 0], ![0, 0, 2]] where
  M :=![![![2, 0, 0], ![0, 2, 0], ![0, 0, 2]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P2P0 : CertificateIrreducibleZModOfList' 2 3 2 1 [1, 0, 1, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 0, 1], [1, 1, 1], [0, 1]]
 g := ![![[]], ![[1, 1]], ![[1, 1]]]
 h' := ![![[0, 0, 1], [0, 1]], ![[1, 1, 1], [0, 0, 1]], ![[0, 1], [1, 1, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1], []]
 b := ![[], [0, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI2N0 : CertifiedPrimeIdeal' SI2N0 2 where
  n := 3
  hpos := by decide
  P := [1, 0, 1, 1]
  hirr := P2P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2690844, -762112, -440046]
  a := ![4, 1, -12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1345422, -381056, -220023]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI2N0 B_one_repr
lemma NI2N0 : Nat.card (O ⧸ I2N0) = 8 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI2N0

def PBC2 : ContainsPrimesAboveP 2 ![I2N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI2N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![2, 0, 0]]) timesTableT_eq_Table B_one_repr 2 (by decide) 𝕀


def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![124997611844304, -4805542100357, 6242288011332]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![124997611844304, -4805542100357, 6242288011332]] 
 ![![3, 0, 0], ![0, 1, 0], ![2, 0, 1]] where
  M :=![![![124997611844304, -4805542100357, 6242288011332], ![-616054462843461, 23684257752017, -30765302880549], ![310575687818761, -11940104463911, 15509919462278]]]
  hmulB := by decide  
  f := ![![![-4452413, -1206206, -600651]], ![![21428123, 2321620, -4019052]], ![![43246736, 9034285, 514763]]]
  g := ![![![37504345273880, -4805542100357, 6242288011332], ![-184841285694121, 23684257752017, -30765302880549], ![93185282964735, -11940104463911, 15509919462278]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N0 : Nat.card (O ⧸ I3N0) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N0)

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := prime_ideal_of_norm_prime hp3.out _ NI3N0

def I3N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![120, -79, -205]] i)))

def SI3N1: IdealEqSpanCertificate' Table ![![120, -79, -205]] 
 ![![3, 0, 0], ![1, 1, 0], ![2, 0, 1]] where
  M :=![![![120, -79, -205], ![20942, 3684, -1121], ![13719, 4418, 3242]]]
  hmulB := by decide  
  f := ![![![-16896106, 649572, -843779]], ![![22125619, -850621, 1104937]], ![![-25257724, 971035, -1261352]]]
  g := ![![![203, -79, -205], ![6500, 3684, -1121], ![939, 4418, 3242]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N1 : Nat.card (O ⧸ I3N1) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N1)

lemma isPrimeI3N1 : Ideal.IsPrime I3N1 := prime_ideal_of_norm_prime hp3.out _ NI3N1
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![124997611844304, -4805542100357, 6242288011332]] ![![120, -79, -205]]
  ![![-16896106, 649572, -843779]] where
 M := ![![![-16896106, 649572, -843779]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI3N1 : IdealMulLeCertificate' Table 
  ![![-16896106, 649572, -843779]] ![![120, -79, -205]]
  ![![3, 0, 0]] where
 M := ![![![3, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-188582634622, 7250072835, -9417676881]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![-188582634622, 7250072835, -9417676881]] 
 ![![5, 0, 0], ![0, 5, 0], ![2, 0, 1]] where
  M :=![![![-188582634622, 7250072835, -9417676881], ![929435146476, -35732200480, 46415301753], ![-468562403667, 18013915020, -23399658856]]]
  hmulB := by decide  
  f := ![![![-84164, -24828, -15375]], ![![1627359, 202039, -254202]], ![![553960, 120609, 16286]]]
  g := ![![![-33949456172, 1450014567, -9417676881], ![167320908594, -7146440096, 46415301753], ![-84352617191, 3602783004, -23399658856]]]
  hle1 := by decide   
  hle2 := by decide  


def P5P0 : CertificateIrreducibleZModOfList' 5 2 2 2 [2, 1, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [4, 4], [0, 1]]
 g := ![![[3, 1], [1]], ![[2, 4], [1]]]
 h' := ![![[4, 4], [3, 4], [0, 1]], ![[0, 1], [4, 1], [4, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2]]
 b := ![[], [3, 1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI5N0 : CertifiedPrimeIdeal' SI5N0 5 where
  n := 2
  hpos := by decide
  P := [2, 1, 1]
  hirr := P5P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![937, -3930, -6819]
  a := ![-7, -3, 20]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2915, -786, -6819]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI5N0 B_one_repr
lemma NI5N0 : Nat.card (O ⧸ I5N0) = 25 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI5N0

def I5N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![84164, 24828, 15375]] i)))

def SI5N1: IdealEqSpanCertificate' Table ![![84164, 24828, 15375]] 
 ![![5, 0, 0], ![3, 1, 0], ![4, 0, 1]] where
  M :=![![![84164, 24828, 15375], ![-1627359, -202039, 254202], ![-2938128, -652701, -112180]]]
  hmulB := by decide  
  f := ![![![188582634622, -7250072835, 9417676881]], ![![-72737448522, 2796396395, -3632454222]], ![![244578588431, -9402841272, 12214073276]]]
  g := ![![![-10364, 24828, 15375], ![-407610, -202039, 254202], ![-106261, -652701, -112180]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N1 : Nat.card (O ⧸ I5N1) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N1)

lemma isPrimeI5N1 : Ideal.IsPrime I5N1 := prime_ideal_of_norm_prime hp5.out _ NI5N1
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![-188582634622, 7250072835, -9417676881]] ![![84164, 24828, 15375]]
  ![![5, 0, 0]] where
 M := ![![![-5, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC5 : ContainsPrimesAboveP 5 ![I5N0, I5N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI5N0
    exact isPrimeI5N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 5 (by decide) (𝕀 ⊙ MulI5N0)

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-938565504, -157504088, 65321759]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![-938565504, -157504088, 65321759]] 
 ![![7, 0, 0], ![0, 1, 0], ![2, 0, 1]] where
  M :=![![![-938565504, -157504088, 65321759], ![-6124985395, -1891531319, -1286893274], ![14078903636, 1697743111, -2298721824]]]
  hmulB := by decide  
  f := ![![![-6532918514290541270, 251158518114164263, -326249104435374233]], ![![4599669141947186392, -176834608143334796, 229704064879532843]], ![![-4185410347703027797, 160908399259735650, -209016287995281926]]]
  g := ![![![-152744146, -157504088, 65321759], ![-507314121, -1891531319, -1286893274], ![2668049612, 1697743111, -2298721824]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N0 : Nat.card (O ⧸ I7N0) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N0)

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := prime_ideal_of_norm_prime hp7.out _ NI7N0

def I7N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-8946, -3077, -2503]] i)))

def SI7N1: IdealEqSpanCertificate' Table ![![-8946, -3077, -2503]] 
 ![![7, 0, 0], ![6, 1, 0], ![1, 0, 1]] where
  M :=![![![-8946, -3077, -2503], ![262034, 36682, -32699], ![380861, 89854, 24948]]]
  hmulB := by decide  
  f := ![![![-3853278482, 148139566, -192429869]], ![![-589810403, 22675303, -29454694]], ![![-1918191188, 73744997, -95793045]]]
  g := ![![![1717, -3077, -2503], ![10663, 36682, -32699], ![-26173, 89854, 24948]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N1 : Nat.card (O ⧸ I7N1) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N1)

lemma isPrimeI7N1 : Ideal.IsPrime I7N1 := prime_ideal_of_norm_prime hp7.out _ NI7N1
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![-938565504, -157504088, 65321759]] ![![-938565504, -157504088, 65321759]]
  ![![2765274194246584500, 556651385398964673, -8774351178665840]] where
 M := ![![![2765274194246584500, 556651385398964673, -8774351178665840]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI7N1 : IdealMulLeCertificate' Table 
  ![![2765274194246584500, 556651385398964673, -8774351178665840]] ![![-8946, -3077, -2503]]
  ![![7, 0, 0]] where
 M := ![![![117781638015644513699642, 11121926872700241241126, -25342327472565302222247]]]
 hmul := by decide  
 g := ![![![![16825948287949216242806, 1588846696100034463018, -3620332496080757460321]]]]
 hle2 := by decide  


def PBC7 : ContainsPrimesAboveP 7 ![I7N0, I7N0, I7N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI7N0
    exact isPrimeI7N0
    exact isPrimeI7N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 7 (by decide) (𝕀 ⊙ MulI7N0 ⊙ MulI7N1)
instance hp11 : Fact (Nat.Prime 11) := {out := by norm_num}

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4025266218620, -154751646798, 201018808985]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![4025266218620, -154751646798, 201018808985]] 
 ![![11, 0, 0], ![0, 11, 0], ![4, 2, 1]] where
  M :=![![![4025266218620, -154751646798, 201018808985], ![-19838644767091, 762698112673, -990727203212], ![10001389675018, -384504139209, 499461981264]]]
  hmulB := by decide  
  f := ![![![638124, 145437, 31661]], ![![-3634072, -45550, 1372255]], ![![-1844663, -223336, 299416]]]
  g := ![![![292835543880, -50617205888, 201018808985], ![-1443248723113, 249468410827, -990727203212], ![727594704542, -125766191067, 499461981264]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P0 : CertificateIrreducibleZModOfList' 11 2 2 3 [9, 3, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [8, 10], [0, 1]]
 g := ![![[4, 5], [5, 9], [1]], ![[0, 6], [0, 2], [1]]]
 h' := ![![[8, 10], [10, 7], [2, 8], [0, 1]], ![[0, 1], [0, 4], [0, 3], [8, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3]]
 b := ![[], [5, 7]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 2
  hpos := by decide
  P := [9, 3, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-123044, -71114, -79161]
  a := ![2, 1, -70]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![17600, 7928, -79161]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N0 B_one_repr
lemma NI11N0 : Nat.card (O ⧸ I11N0) = 121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N0

def I11N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![638124, 145437, 31661]] i)))

def SI11N1: IdealEqSpanCertificate' Table ![![638124, 145437, 31661]] 
 ![![11, 0, 0], ![2, 1, 0], ![8, 0, 1]] where
  M :=![![![638124, 145437, 31661], ![-3634072, -45550, 1372255], ![-15575645, -2947344, 422422]]]
  hmulB := by decide  
  f := ![![![4025266218620, -154751646798, 201018808985]], ![![-1071646575441, 41199529007, -53517235022]], ![![3836683583998, -147501573963, 191601132104]]]
  g := ![![![8542, 145437, 31661], ![-1320092, -45550, 1372255], ![-1187303, -2947344, 422422]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N1 : Nat.card (O ⧸ I11N1) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N1)

lemma isPrimeI11N1 : Ideal.IsPrime I11N1 := prime_ideal_of_norm_prime hp11.out _ NI11N1
def MulI11N0 : IdealMulLeCertificate' Table 
  ![![4025266218620, -154751646798, 201018808985]] ![![638124, 145437, 31661]]
  ![![11, 0, 0]] where
 M := ![![![11, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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
instance hp13 : Fact (Nat.Prime 13) := {out := by norm_num}

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2097408, -80635, 104743]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![2097408, -80635, 104743]] 
 ![![13, 0, 0], ![0, 13, 0], ![7, 2, 1]] where
  M :=![![![2097408, -80635, 104743], ![-10337138, 397412, -516229], ![5211331, -200350, 260250]]]
  hmulB := by decide  
  f := ![![![-550, -100, 23]], ![![-2023, -841, -854]], ![![120, -79, -205]]]
  g := ![![![104939, -22317, 104743], ![-517195, 109990, -516229], ![260737, -55450, 260250]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P0 : CertificateIrreducibleZModOfList' 13 2 2 3 [9, 8, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [5, 12], [0, 1]]
 g := ![![[11, 3], [9], [5, 1]], ![[0, 10], [9], [10, 12]]]
 h' := ![![[5, 12], [7, 9], [7, 3], [0, 1]], ![[0, 1], [0, 4], [9, 10], [5, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11]]
 b := ![[], [9, 12]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 2
  hpos := by decide
  P := [9, 8, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-764, -5526, -9211]
  a := ![8, 3, -23]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![4901, 992, -9211]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N0 B_one_repr
lemma NI13N0 : Nat.card (O ⧸ I13N0) = 169 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N0

def I13N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![550, 100, -23]] i)))

def SI13N1: IdealEqSpanCertificate' Table ![![550, 100, -23]] 
 ![![13, 0, 0], ![6, 1, 0], ![5, 0, 1]] where
  M :=![![![550, 100, -23], ![2023, 841, 854], ![-9456, -1355, 1118]]]
  hmulB := by decide  
  f := ![![![-2097408, 80635, -104743]], ![![-172870, 6646, -8633]], ![![-1207567, 46425, -60305]]]
  g := ![![![5, 100, -23], ![-561, 841, 854], ![-532, -1355, 1118]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N1 : Nat.card (O ⧸ I13N1) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N1)

lemma isPrimeI13N1 : Ideal.IsPrime I13N1 := prime_ideal_of_norm_prime hp13.out _ NI13N1
def MulI13N0 : IdealMulLeCertificate' Table 
  ![![2097408, -80635, 104743]] ![![550, 100, -23]]
  ![![13, 0, 0]] where
 M := ![![![-13, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC13 : ContainsPrimesAboveP 13 ![I13N0, I13N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI13N0
    exact isPrimeI13N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 13 (by decide) (𝕀 ⊙ MulI13N0)
instance hp17 : Fact (Nat.Prime 17) := {out := by norm_num}

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-181, 7, -9]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![-181, 7, -9]] 
 ![![17, 0, 0], ![0, 17, 0], ![5, 3, 1]] where
  M :=![![![-181, 7, -9], ![888, -35, 45], ![-455, 16, -23]]]
  hmulB := by decide  
  f := ![![![-5, -1, 0]], ![![3, -4, -9]], ![![5, 0, -2]]]
  g := ![![![-8, 2, -9], ![39, -10, 45], ![-20, 5, -23]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P0 : CertificateIrreducibleZModOfList' 17 2 2 4 [2, 7, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [10, 16], [0, 1]]
 g := ![![[12, 9], [13], [15], [1]], ![[0, 8], [13], [15], [1]]]
 h' := ![![[10, 16], [4, 3], [8, 8], [15, 10], [0, 1]], ![[0, 1], [0, 14], [3, 9], [13, 7], [10, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14]]
 b := ![[], [16, 7]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 2
  hpos := by decide
  P := [2, 7, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1565, -1738, -2523]
  a := ![4, 1, -12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![650, 343, -2523]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N0 B_one_repr
lemma NI17N0 : Nat.card (O ⧸ I17N0) = 289 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N0

def I17N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 1, 0]] i)))

def SI17N1: IdealEqSpanCertificate' Table ![![5, 1, 0]] 
 ![![17, 0, 0], ![5, 1, 0], ![5, 0, 1]] where
  M :=![![![5, 1, 0], ![-3, 4, 9], ![-101, -17, 7]]]
  hmulB := by decide  
  f := ![![![181, -7, 9]], ![![1, 0, 0]], ![![80, -3, 4]]]
  g := ![![![0, 1, 0], ![-4, 4, 9], ![-3, -17, 7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N1 : Nat.card (O ⧸ I17N1) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N1)

lemma isPrimeI17N1 : Ideal.IsPrime I17N1 := prime_ideal_of_norm_prime hp17.out _ NI17N1
def MulI17N0 : IdealMulLeCertificate' Table 
  ![![-181, 7, -9]] ![![5, 1, 0]]
  ![![17, 0, 0]] where
 M := ![![![-17, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC17 : ContainsPrimesAboveP 17 ![I17N0, I17N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI17N0
    exact isPrimeI17N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 17 (by decide) (𝕀 ⊙ MulI17N0)
instance hp19 : Fact (Nat.Prime 19) := {out := by norm_num}

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![19, 0, 0]] 
 ![![19, 0, 0], ![0, 19, 0], ![0, 0, 19]] where
  M :=![![![19, 0, 0], ![0, 19, 0], ![0, 0, 19]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P0 : CertificateIrreducibleZModOfList' 19 3 2 4 [12, 2, 17, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [16, 15, 15], [5, 3, 4], [0, 1]]
 g := ![![[5], [2, 1, 4], [2, 1], []], ![[8, 1, 15, 3], [11, 12, 7, 8], [9, 9], [7, 16]], ![[8, 5, 11, 16], [17, 7, 9, 7], [1, 16], [18, 16]]]
 h' := ![![[16, 15, 15], [14, 9], [14, 3, 2], [0, 0, 1], [0, 1]], ![[5, 3, 4], [6, 2, 2], [7, 4, 13], [1, 8, 3], [16, 15, 15]], ![[0, 1], [2, 8, 17], [8, 12, 4], [18, 11, 15], [5, 3, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9, 15], []]
 b := ![[], [4, 15, 18], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 3
  hpos := by decide
  P := [12, 2, 17, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![573493074, 148553305, 65349474]
  a := ![-22, -1, 67]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![30183846, 7818595, 3439446]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N0 B_one_repr
lemma NI19N0 : Nat.card (O ⧸ I19N0) = 6859 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N0

def PBC19 : ContainsPrimesAboveP 19 ![I19N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI19N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![19, 0, 0]]) timesTableT_eq_Table B_one_repr 19 (by decide) 𝕀

instance hp23 : Fact (Nat.Prime 23) := {out := by norm_num}

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-11192941, -1954113, 628674]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![-11192941, -1954113, 628674]] 
 ![![23, 0, 0], ![0, 23, 0], ![19, 7, 1]] where
  M :=![![![-11192941, -1954113, 628674], ![-57633735, -19926286, -16329669], ![179762541, 23789811, -25159951]]]
  hmulB := by decide  
  f := ![![![-38688005155415, 1487363116863, -1932050278407]], ![![190674988768518, -7330513539359, 9522167494953]], ![![21892458974738, -841657146334, 1093293161207]]]
  g := ![![![-1005989, -276297, 628674], ![10983912, 4103539, -16329669], ![28600070, 8691716, -25159951]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P0 : CertificateIrreducibleZModOfList' 23 2 2 4 [21, 14, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [9, 22], [0, 1]]
 g := ![![[16, 2], [16, 8], [6, 12], [1]], ![[11, 21], [19, 15], [22, 11], [1]]]
 h' := ![![[9, 22], [9, 5], [12, 13], [2, 9], [0, 1]], ![[0, 1], [8, 18], [14, 10], [14, 14], [9, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9]]
 b := ![[], [20, 16]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 2
  hpos := by decide
  P := [21, 14, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![192, 32, -25]
  a := ![0, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![29, 9, -25]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N0 B_one_repr
lemma NI23N0 : Nat.card (O ⧸ I23N0) = 529 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N0

def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![38688005155415, -1487363116863, 1932050278407]] i)))

def SI23N1: IdealEqSpanCertificate' Table ![![38688005155415, -1487363116863, 1932050278407]] 
 ![![23, 0, 0], ![4, 1, 0], ![6, 0, 1]] where
  M :=![![![38688005155415, -1487363116863, 1932050278407], ![-190674988768518, 7330513539359, -9522167494953], ![96126267007767, -3695581189434, 4800474467177]]]
  hmulB := by decide  
  f := ![![![11192941, 1954113, -628674]], ![![4452413, 1206206, 600651]], ![![-4895865, -524571, 929909]]]
  g := ![![![1436745910975, -1487363116863, 1932050278407], ![-7081045128532, 7330513539359, -9522167494953], ![3569814998367, -3695581189434, 4800474467177]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N1 : Nat.card (O ⧸ I23N1) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N1)

lemma isPrimeI23N1 : Ideal.IsPrime I23N1 := prime_ideal_of_norm_prime hp23.out _ NI23N1
def MulI23N0 : IdealMulLeCertificate' Table 
  ![![-11192941, -1954113, 628674]] ![![38688005155415, -1487363116863, 1932050278407]]
  ![![23, 0, 0]] where
 M := ![![![-23, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC23 : ContainsPrimesAboveP 23 ![I23N0, I23N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI23N0
    exact isPrimeI23N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 23 (by decide) (𝕀 ⊙ MulI23N0)
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


def P29P0 : CertificateIrreducibleZModOfList' 29 3 2 4 [19, 25, 20, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [22, 17, 11], [16, 11, 18], [0, 1]]
 g := ![![[8, 10, 28], [15, 25], [15, 18, 23], [1]], ![[1, 0, 15, 21], [8, 4], [18, 6, 27, 15], [8, 17, 25, 26]], ![[18, 22, 21, 21], [26, 9], [16, 27, 24, 12], [4, 17, 18, 3]]]
 h' := ![![[22, 17, 11], [1, 27, 17], [5, 21, 24], [10, 4, 9], [0, 1]], ![[16, 11, 18], [13, 3, 20], [7, 22, 2], [27, 4, 27], [22, 17, 11]], ![[0, 1], [5, 28, 21], [8, 15, 3], [18, 21, 22], [16, 11, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [23, 19], []]
 b := ![[], [25, 21, 22], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 3
  hpos := by decide
  P := [19, 25, 20, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![13757890, 3875792, 2242860]
  a := ![-7, -2, 21]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![474410, 133648, 77340]
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

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![31, 0, 0]] 
 ![![31, 0, 0], ![0, 31, 0], ![0, 0, 31]] where
  M :=![![![31, 0, 0], ![0, 31, 0], ![0, 0, 31]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P0 : CertificateIrreducibleZModOfList' 31 3 2 4 [16, 4, 21, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [29, 9, 12], [12, 21, 19], [0, 1]]
 g := ![![[4, 28, 16], [1, 23, 10], [2, 21, 7], [1]], ![[30, 29, 19, 22], [15, 4, 20, 13], [14, 29, 26, 30], [19, 19, 26, 23]], ![[13, 18, 7, 4], [15, 14, 30, 25], [21, 27, 18, 4], [20, 10, 7, 8]]]
 h' := ![![[29, 9, 12], [15, 1, 27], [30, 5, 14], [15, 27, 10], [0, 1]], ![[12, 21, 19], [23, 29, 21], [16, 6, 13], [29, 7, 7], [29, 9, 12]], ![[0, 1], [21, 1, 14], [18, 20, 4], [13, 28, 14], [12, 21, 19]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [24, 17], []]
 b := ![[], [21, 20, 27], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 3
  hpos := by decide
  P := [16, 4, 21, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-260059, -69750, -33170]
  a := ![0, 0, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-8389, -2250, -1070]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N0 B_one_repr
lemma NI31N0 : Nat.card (O ⧸ I31N0) = 29791 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N0

def PBC31 : ContainsPrimesAboveP 31 ![I31N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI31N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![31, 0, 0]]) timesTableT_eq_Table B_one_repr 31 (by decide) 𝕀



lemma PB197I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 31 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 31 (by omega)

def PB197I0 : PrimesBelowBoundCertificateInterval O 1 31 197 where
  m := 11
  g := ![1, 3, 2, 3, 2, 2, 2, 1, 2, 1, 1]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]
  hP := PB197I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0]
    · exact ![I3N0, I3N1, I3N1]
    · exact ![I5N0, I5N1]
    · exact ![I7N0, I7N0, I7N1]
    · exact ![I11N0, I11N1]
    · exact ![I13N0, I13N1]
    · exact ![I17N0, I17N1]
    · exact ![I19N0]
    · exact ![I23N0, I23N1]
    · exact ![I29N0]
    · exact ![I31N0]
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
    · exact ![8]
    · exact ![3, 3, 3]
    · exact ![25, 5]
    · exact ![7, 7, 7]
    · exact ![121, 11]
    · exact ![169, 13]
    · exact ![289, 17]
    · exact ![6859]
    · exact ![529, 23]
    · exact ![24389]
    · exact ![29791]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI2N0
    · dsimp ; intro j
      fin_cases j
      exact NI3N0
      exact NI3N1
      exact NI3N1
    · dsimp ; intro j
      fin_cases j
      exact NI5N0
      exact NI5N1
    · dsimp ; intro j
      fin_cases j
      exact NI7N0
      exact NI7N0
      exact NI7N1
    · dsimp ; intro j
      fin_cases j
      exact NI11N0
      exact NI11N1
    · dsimp ; intro j
      fin_cases j
      exact NI13N0
      exact NI13N1
    · dsimp ; intro j
      fin_cases j
      exact NI17N0
      exact NI17N1
    · dsimp ; intro j
      fin_cases j
      exact NI19N0
    · dsimp ; intro j
      fin_cases j
      exact NI23N0
      exact NI23N1
    · dsimp ; intro j
      fin_cases j
      exact NI29N0
    · dsimp ; intro j
      fin_cases j
      exact NI31N0
  β := ![I2N0, I3N0, I3N1, I5N0, I5N1, I7N0, I7N1, I11N0, I11N1, I13N0, I13N1, I17N1, I23N1]
  Il := ![[I2N0], [I3N0, I3N1, I3N1], [I5N0, I5N1], [I7N0, I7N0, I7N1], [I11N0, I11N1], [I13N0, I13N1], [I17N1], [], [I23N1], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
