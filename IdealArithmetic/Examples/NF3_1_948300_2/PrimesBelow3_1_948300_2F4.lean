
import IdealArithmetic.Examples.NF3_1_948300_2.RI3_1_948300_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp197 : Fact (Nat.Prime 197) := {out := by norm_num}

def I197N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![197, 0, 0], ![34, -80, 1]] i)))

def SI197N0: IdealEqSpanCertificate' Table ![![197, 0, 0], ![34, -80, 1]] 
 ![![197, 0, 0], ![0, 197, 0], ![34, 117, 1]] where
  M :=![![![197, 0, 0], ![0, 197, 0], ![0, 0, 197]], ![![34, -80, 1], ![277, -26, -241], ![-15898, -1541, 135]]]
  hmulB := by decide  
  f := ![![![-33, 80, -1], ![197, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-34, -117, 197]], ![![0, -1, 1], ![43, 143, -241], ![-104, -88, 135]]]
  hle1 := by decide   
  hle2 := by decide  


def P197P0 : CertificateIrreducibleZModOfList' 197 2 2 7 [75, 1, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [196, 196], [0, 1]]
 g := ![![[176, 6], [28], [73, 190], [137], [193], [157], [196, 1]], ![[170, 191], [28], [80, 7], [137], [193], [157], [195, 196]]]
 h' := ![![[196, 196], [172, 20], [41, 15], [96, 105], [179, 48], [154, 169], [75, 123], [0, 1]], ![[0, 1], [152, 177], [26, 182], [188, 92], [131, 149], [182, 28], [149, 74], [196, 196]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [170]]
 b := ![[], [141, 85]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI197N0 : CertifiedPrimeIdeal' SI197N0 197 where
  n := 2
  hpos := by decide
  P := [75, 1, 1]
  hirr := P197P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1195, 769, 180]
  a := ![1, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-25, -103, 180]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI197N0 : Ideal.IsPrime I197N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI197N0 B_one_repr
lemma NI197N0 : Nat.card (O ⧸ I197N0) = 38809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI197N0

def I197N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![197, 0, 0], ![44, 1, 0]] i)))

def SI197N1: IdealEqSpanCertificate' Table ![![197, 0, 0], ![44, 1, 0]] 
 ![![197, 0, 0], ![44, 1, 0], ![62, 0, 1]] where
  M :=![![![197, 0, 0], ![0, 197, 0], ![0, 0, 197]], ![![44, 1, 0], ![-1, 45, 3], ![197, 20, 43]]]
  hmulB := by decide  
  f := ![![![-455, 18539, 1236], ![197, -81164, 0]], ![![-92, 4140, 276], ![1, -18124, 0]], ![![-170, 5834, 389], ![182, -25544, 0]]]
  g := ![![![1, 0, 0], ![-44, 197, 0], ![-62, 0, 197]], ![![0, 1, 0], ![-11, 45, 3], ![-17, 20, 43]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI197N1 : Nat.card (O ⧸ I197N1) = 197 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI197N1)

lemma isPrimeI197N1 : Ideal.IsPrime I197N1 := prime_ideal_of_norm_prime hp197.out _ NI197N1
def MulI197N0 : IdealMulLeCertificate' Table 
  ![![197, 0, 0], ![34, -80, 1]] ![![197, 0, 0], ![44, 1, 0]]
  ![![197, 0, 0]] where
 M := ![![![38809, 0, 0], ![8668, 197, 0]], ![![6698, -15760, 197], ![1773, -3546, -197]]]
 hmul := by decide  
 g := ![![![![197, 0, 0]], ![![44, 1, 0]]], ![![![34, -80, 1]], ![![9, -18, -1]]]]
 hle2 := by decide  


def PBC197 : ContainsPrimesAboveP 197 ![I197N0, I197N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI197N0
    exact isPrimeI197N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 197 (by decide) (𝕀 ⊙ MulI197N0)
instance hp199 : Fact (Nat.Prime 199) := {out := by norm_num}

def I199N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1797845, -152134, -4738]] i)))

def SI199N0: IdealEqSpanCertificate' Table ![![1797845, -152134, -4738]] 
 ![![199, 0, 0], ![0, 199, 0], ![133, 165, 1]] where
  M :=![![![1797845, -152134, -4738], ![-781252, 1550951, -451664], ![-29316554, -3322222, 1850481]]]
  hmulB := by decide  
  f := ![![![-6881795377, -1493777710, -382220386]], ![![-73803638332, -16019980807, -4099112744]], ![![-67007069877, -14544702641, -3721625929]]]
  g := ![![![12201, 3164, -4738], ![297940, 382289, -451664], ![-1384073, -1551013, 1850481]]]
  hle1 := by decide   
  hle2 := by decide  


def P199P0 : CertificateIrreducibleZModOfList' 199 2 2 7 [33, 187, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [12, 198], [0, 1]]
 g := ![![[72, 193], [61, 111], [151, 4], [102], [89], [182], [12, 1]], ![[0, 6], [0, 88], [0, 195], [102], [89], [182], [24, 198]]]
 h' := ![![[12, 198], [176, 118], [191, 67], [175, 2], [77, 36], [167, 41], [2, 111], [0, 1]], ![[0, 1], [0, 81], [0, 132], [0, 197], [111, 163], [62, 158], [140, 88], [12, 198]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [66]]
 b := ![[], [1, 33]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI199N0 : CertifiedPrimeIdeal' SI199N0 199 where
  n := 2
  hpos := by decide
  P := [33, 187, 1]
  hirr := P199P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-9351, 3776, 2792]
  a := ![-3, 0, 8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1913, -2296, 2792]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI199N0 : Ideal.IsPrime I199N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI199N0 B_one_repr
lemma NI199N0 : Nat.card (O ⧸ I199N0) = 39601 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI199N0

def I199N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-6881795377, -1493777710, -382220386]] i)))

def SI199N1: IdealEqSpanCertificate' Table ![![-6881795377, -1493777710, -382220386]] 
 ![![199, 0, 0], ![103, 1, 0], ![11, 0, 1]] where
  M :=![![![-6881795377, -1493777710, -382220386], ![-73803638332, -16019980807, -4099112744], ![-241527795602, -52426556974, -13414645773]]]
  hmulB := by decide  
  f := ![![![1797845, -152134, -4738]], ![![926617, -70949, -4722]], ![![-47941, -25104, 9037]]]
  g := ![![![759707201, -1493777710, -382220386], ![8147460427, -16019980807, -4099112744], ![26663159177, -52426556974, -13414645773]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI199N1 : Nat.card (O ⧸ I199N1) = 199 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI199N1)

lemma isPrimeI199N1 : Ideal.IsPrime I199N1 := prime_ideal_of_norm_prime hp199.out _ NI199N1
def MulI199N0 : IdealMulLeCertificate' Table 
  ![![1797845, -152134, -4738]] ![![-6881795377, -1493777710, -382220386]]
  ![![199, 0, 0]] where
 M := ![![![199, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC199 : ContainsPrimesAboveP 199 ![I199N0, I199N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI199N0
    exact isPrimeI199N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 199 (by decide) (𝕀 ⊙ MulI199N0)
instance hp211 : Fact (Nat.Prime 211) := {out := by norm_num}

def I211N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109434526072, 6333083772, -5053292673]] i)))

def SI211N0: IdealEqSpanCertificate' Table ![![109434526072, 6333083772, -5053292673]] 
 ![![211, 0, 0], ![0, 211, 0], ![203, 56, 1]] where
  M :=![![![109434526072, 6333083772, -5053292673], ![-1001831740353, 14701756384, 24052543989], ![1944971891958, -171482592267, -3017703833]]]
  hmulB := by decide  
  f := ![![![19337568944350425181, 4197455441816834397, 1074023951789337540]], ![![207385263060682660983, 45015503421954010378, 11518342373661165651]], ![![76861538596172289680, 16683735394834832069, 4268950955584694200]]]
  g := ![![![5380345681, 1371172860, -5053292673], ![-27888616920, -6313937000, 24052543989], ![12121164787, -11806529, -3017703833]]]
  hle1 := by decide   
  hle2 := by decide  


def P211P0 : CertificateIrreducibleZModOfList' 211 2 2 7 [126, 2, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [209, 210], [0, 1]]
 g := ![![[67, 139], [172, 1], [58], [79], [32, 55], [114], [209, 1]], ![[0, 72], [170, 210], [58], [79], [133, 156], [114], [207, 210]]]
 h' := ![![[209, 210], [61, 136], [124, 210], [70, 144], [188, 76], [188, 107], [41, 89], [0, 1]], ![[0, 1], [0, 75], [126, 1], [204, 67], [36, 135], [185, 104], [74, 122], [209, 210]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [184]]
 b := ![[], [92, 92]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI211N0 : CertifiedPrimeIdeal' SI211N0 211 where
  n := 2
  hpos := by decide
  P := [126, 2, 1]
  hirr := P211P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1066023, 440211, 97713]
  a := ![1, -64, -67]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-88956, -23847, 97713]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI211N0 : Ideal.IsPrime I211N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI211N0 B_one_repr
lemma NI211N0 : Nat.card (O ⧸ I211N0) = 44521 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI211N0

def I211N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1060033151, -23303182, -23082526]] i)))

def SI211N1: IdealEqSpanCertificate' Table ![![1060033151, -23303182, -23082526]] 
 ![![211, 0, 0], ![44, 1, 0], ![43, 0, 1]] where
  M :=![![![1060033151, -23303182, -23082526], ![-4523954440, 575079449, -46827020], ![-1405338266, -1827932674, 598603287]]]
  hmulB := by decide  
  f := ![![![-258647808573497383, -56142664816613758, -14365504903185814]], ![![-67082300371302732, -14561032338316743, -3725804290458916]], ![![-95732327302813533, -20779870486893980, -5317049561899411]]]
  g := ![![![14587307, -23303182, -23082526], ![-131819376, 575079449, -46827020], ![252529659, -1827932674, 598603287]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI211N1 : Nat.card (O ⧸ I211N1) = 211 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI211N1)

lemma isPrimeI211N1 : Ideal.IsPrime I211N1 := prime_ideal_of_norm_prime hp211.out _ NI211N1
def MulI211N0 : IdealMulLeCertificate' Table 
  ![![109434526072, 6333083772, -5053292673]] ![![1060033151, -23303182, -23082526]]
  ![![211, 0, 0]] where
 M := ![![![94455228613726790210, 10328932436194538126, -5847502338038553463]]]
 hmul := by decide  
 g := ![![![![447655111913397110, 48952286427462266, -27713281222931533]]]]
 hle2 := by decide  


def PBC211 : ContainsPrimesAboveP 211 ![I211N0, I211N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI211N0
    exact isPrimeI211N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 211 (by decide) (𝕀 ⊙ MulI211N0)
instance hp223 : Fact (Nat.Prime 223) := {out := by norm_num}

def I223N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![223, 0, 0], ![6, 1, 0]] i)))

def SI223N0: IdealEqSpanCertificate' Table ![![223, 0, 0], ![6, 1, 0]] 
 ![![223, 0, 0], ![6, 1, 0], ![60, 0, 1]] where
  M :=![![![223, 0, 0], ![0, 223, 0], ![0, 0, 223]], ![![6, 1, 0], ![-1, 7, 3], ![197, 20, 5]]]
  hmulB := by decide  
  f := ![![![-9677, 67703, 29016], ![223, -2156856, 0]], ![![-266, 1819, 780], ![224, -57980, 0]], ![![-2604, 18216, 7807], ![72, -580320, 0]]]
  g := ![![![1, 0, 0], ![-6, 223, 0], ![-60, 0, 223]], ![![0, 1, 0], ![-1, 7, 3], ![-1, 20, 5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI223N0 : Nat.card (O ⧸ I223N0) = 223 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI223N0)

lemma isPrimeI223N0 : Ideal.IsPrime I223N0 := prime_ideal_of_norm_prime hp223.out _ NI223N0

def I223N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![797566189900174, 173121479418625, 44297460221359]] i)))

def SI223N1: IdealEqSpanCertificate' Table ![![797566189900174, 173121479418625, 44297460221359]] 
 ![![223, 0, 0], ![13, 1, 0], ![162, 0, 1]] where
  M :=![![![797566189900174, 173121479418625, 44297460221359], ![8553478184189098, 1856636873745979, 475066978034516], ![27991881934921583, 6075979741432681, 1554691375130088]]]
  hmulB := by decide  
  f := ![![![-316501244, 71744479, -12904961]], ![![-30172816, 1927454, 270735]], ![![-158558989, 55139473, -12331182]]]
  g := ![![![-38695971293283, 173121479418625, 44297460221359], ![-414993953435427, 1856636873745979, 475066978034516], ![-1358098015581962, 6075979741432681, 1554691375130088]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI223N1 : Nat.card (O ⧸ I223N1) = 223 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI223N1)

lemma isPrimeI223N1 : Ideal.IsPrime I223N1 := prime_ideal_of_norm_prime hp223.out _ NI223N1

def I223N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![223, 0, 0], ![-19, 1, 0]] i)))

def SI223N2: IdealEqSpanCertificate' Table ![![223, 0, 0], ![-19, 1, 0]] 
 ![![223, 0, 0], ![204, 1, 0], ![183, 0, 1]] where
  M :=![![![223, 0, 0], ![0, 223, 0], ![0, 0, 223]], ![![-19, 1, 0], ![-1, -18, 3], ![197, 20, -20]]]
  hmulB := by decide  
  f := ![![![-4204, -76033, 12672], ![223, -941952, 0]], ![![-3844, -69553, 11592], ![224, -861672, 0]], ![![-3446, -62395, 10399], ![229, -772992, 0]]]
  g := ![![![1, 0, 0], ![-204, 223, 0], ![-183, 0, 223]], ![![-1, 1, 0], ![14, -18, 3], ![-1, 20, -20]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI223N2 : Nat.card (O ⧸ I223N2) = 223 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI223N2)

lemma isPrimeI223N2 : Ideal.IsPrime I223N2 := prime_ideal_of_norm_prime hp223.out _ NI223N2
def MulI223N0 : IdealMulLeCertificate' Table 
  ![![223, 0, 0], ![6, 1, 0]] ![![797566189900174, 173121479418625, 44297460221359]]
  ![![223, 0, 0], ![-123, 81, 1]] where
 M := ![![![177857260347738802, 38606089910353375, 9878333629363057]], ![![13338875323590142, 2895365750257729, 740851739362670]]]
 hmul := by decide  
 g := ![![![![652843129133692, 268426909679479, 45474070471493], ![-262384085779882, 0, 0]]], ![![![48961695959746, 20131385554399, 3410448104786], ![-19678188004608, 0, 0]]]]
 hle2 := by decide  

def MulI223N1 : IdealMulLeCertificate' Table 
  ![![223, 0, 0], ![-123, 81, 1]] ![![223, 0, 0], ![-19, 1, 0]]
  ![![223, 0, 0]] where
 M := ![![![49729, 0, 0], ![-4237, 223, 0]], ![![-27429, 18063, 223], ![2453, -1561, 223]]]
 hmul := by decide  
 g := ![![![![223, 0, 0]], ![![-19, 1, 0]]], ![![![-123, 81, 1]], ![![11, -7, 1]]]]
 hle2 := by decide  


def PBC223 : ContainsPrimesAboveP 223 ![I223N0, I223N1, I223N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI223N0
    exact isPrimeI223N1
    exact isPrimeI223N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 223 (by decide) (𝕀 ⊙ MulI223N0 ⊙ MulI223N1)
instance hp227 : Fact (Nat.Prime 227) := {out := by norm_num}

def I227N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![227, 0, 0], ![-32, 58, 1]] i)))

def SI227N0: IdealEqSpanCertificate' Table ![![227, 0, 0], ![-32, 58, 1]] 
 ![![227, 0, 0], ![0, 227, 0], ![195, 58, 1]] where
  M :=![![![227, 0, 0], ![0, 227, 0], ![0, 0, 227]], ![![-32, 58, 1], ![139, 46, 173], ![11288, 1219, -69]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-195, -58, 227]], ![![-1, 0, 1], ![-148, -44, 173], ![109, 23, -69]]]
  hle1 := by decide   
  hle2 := by decide  


def P227P0 : CertificateIrreducibleZModOfList' 227 2 2 7 [94, 20, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [207, 226], [0, 1]]
 g := ![![[63, 166], [199, 103], [176], [40], [30], [154, 112], [207, 1]], ![[148, 61], [182, 124], [176], [40], [30], [184, 115], [187, 226]]]
 h' := ![![[207, 226], [135, 47], [166, 28], [162, 67], [111, 99], [52, 22], [64, 79], [0, 1]], ![[0, 1], [103, 180], [60, 199], [184, 160], [174, 128], [66, 205], [73, 148], [207, 226]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [189]]
 b := ![[], [37, 208]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI227N0 : CertifiedPrimeIdeal' SI227N0 227 where
  n := 2
  hpos := by decide
  P := [94, 20, 1]
  hirr := P227P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5518, 4071, 1123]
  a := ![3, -1, -8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-989, -269, 1123]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI227N0 : Ideal.IsPrime I227N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI227N0 B_one_repr
lemma NI227N0 : Nat.card (O ⧸ I227N0) = 51529 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI227N0

def I227N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![227, 0, 0], ![54, 1, 0]] i)))

def SI227N1: IdealEqSpanCertificate' Table ![![227, 0, 0], ![54, 1, 0]] 
 ![![227, 0, 0], ![54, 1, 0], ![69, 0, 1]] where
  M :=![![![227, 0, 0], ![0, 227, 0], ![0, 0, 227]], ![![54, 1, 0], ![-1, 55, 3], ![197, 20, 53]]]
  hmulB := by decide  
  f := ![![![4121, -226600, -12360], ![0, 935240, 0]], ![![980, -53900, -2940], ![1, 222460, 0]], ![![1221, -68879, -3757], ![133, 284280, 0]]]
  g := ![![![1, 0, 0], ![-54, 227, 0], ![-69, 0, 227]], ![![0, 1, 0], ![-14, 55, 3], ![-20, 20, 53]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI227N1 : Nat.card (O ⧸ I227N1) = 227 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI227N1)

lemma isPrimeI227N1 : Ideal.IsPrime I227N1 := prime_ideal_of_norm_prime hp227.out _ NI227N1
def MulI227N0 : IdealMulLeCertificate' Table 
  ![![227, 0, 0], ![-32, 58, 1]] ![![227, 0, 0], ![54, 1, 0]]
  ![![227, 0, 0]] where
 M := ![![![51529, 0, 0], ![12258, 227, 0]], ![![-7264, 13166, 227], ![-1589, 3178, 227]]]
 hmul := by decide  
 g := ![![![![227, 0, 0]], ![![54, 1, 0]]], ![![![-32, 58, 1]], ![![-7, 14, 1]]]]
 hle2 := by decide  


def PBC227 : ContainsPrimesAboveP 227 ![I227N0, I227N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI227N0
    exact isPrimeI227N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 227 (by decide) (𝕀 ⊙ MulI227N0)
instance hp229 : Fact (Nat.Prime 229) := {out := by norm_num}

def I229N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![229, 0, 0]] i)))

def SI229N0: IdealEqSpanCertificate' Table ![![229, 0, 0]] 
 ![![229, 0, 0], ![0, 229, 0], ![0, 0, 229]] where
  M :=![![![229, 0, 0], ![0, 229, 0], ![0, 0, 229]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P229P0 : CertificateIrreducibleZModOfList' 229 3 2 7 [18, 167, 120, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [24, 45, 23], [85, 183, 206], [0, 1]]
 g := ![![[75, 95, 78], [116, 78], [214, 215, 126], [86, 9], [105, 15], [207, 39, 202], [1]], ![[54, 28, 212, 41], [88, 33], [70, 123, 31, 10], [121, 43], [25, 158], [120, 37, 10, 28], [79, 81, 31, 30]], ![[140, 167, 138, 59], [78, 203], [177, 122, 160, 10], [160, 165], [124, 14], [3, 217, 204, 127], [56, 52, 214, 199]]]
 h' := ![![[24, 45, 23], [51, 150, 188], [41, 177, 41], [54, 70, 85], [122, 118, 3], [167, 90, 106], [211, 62, 109], [0, 1]], ![[85, 183, 206], [81, 87, 69], [73, 201, 124], [59, 146, 219], [93, 201, 57], [90, 91, 171], [36, 134, 76], [24, 45, 23]], ![[0, 1], [28, 221, 201], [150, 80, 64], [123, 13, 154], [22, 139, 169], [184, 48, 181], [84, 33, 44], [85, 183, 206]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [56, 15], []]
 b := ![[], [63, 37, 79], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI229N0 : CertifiedPrimeIdeal' SI229N0 229 where
  n := 3
  hpos := by decide
  P := [18, 167, 120, 1]
  hirr := P229P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-314875, 3206, 4809]
  a := ![1, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1375, 14, 21]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI229N0 : Ideal.IsPrime I229N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI229N0 B_one_repr
lemma NI229N0 : Nat.card (O ⧸ I229N0) = 12008989 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI229N0

def PBC229 : ContainsPrimesAboveP 229 ![I229N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI229N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![229, 0, 0]]) timesTableT_eq_Table B_one_repr 229 (by decide) 𝕀

instance hp233 : Fact (Nat.Prime 233) := {out := by norm_num}

def I233N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![233, 0, 0], ![-104, -46, 1]] i)))

def SI233N0: IdealEqSpanCertificate' Table ![![233, 0, 0], ![-104, -46, 1]] 
 ![![233, 0, 0], ![0, 233, 0], ![129, 187, 1]] where
  M :=![![![233, 0, 0], ![0, 233, 0], ![0, 0, 233]], ![![-104, -46, 1], ![243, -130, -139], ![-9200, -861, -37]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-129, -187, 233]], ![![-1, -1, 1], ![78, 111, -139], ![-19, 26, -37]]]
  hle1 := by decide   
  hle2 := by decide  


def P233P0 : CertificateIrreducibleZModOfList' 233 2 2 7 [141, 33, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [200, 232], [0, 1]]
 g := ![![[144, 195], [110], [100], [213, 98], [187], [182, 23], [200, 1]], ![[0, 38], [110], [100], [8, 135], [187], [122, 210], [167, 232]]]
 h' := ![![[200, 232], [201, 112], [223, 209], [24, 10], [54, 129], [201, 120], [226, 16], [0, 1]], ![[0, 1], [0, 121], [83, 24], [160, 223], [224, 104], [202, 113], [164, 217], [200, 232]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [150]]
 b := ![[], [189, 75]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI233N0 : CertifiedPrimeIdeal' SI233N0 233 where
  n := 2
  hpos := by decide
  P := [141, 33, 1]
  hirr := P233P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![30556, 5396, 1615]
  a := ![-1, 21, 4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-763, -1273, 1615]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI233N0 : Ideal.IsPrime I233N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI233N0 B_one_repr
lemma NI233N0 : Nat.card (O ⧸ I233N0) = 54289 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI233N0

def I233N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![233, 0, 0], ![-94, 1, 0]] i)))

def SI233N1: IdealEqSpanCertificate' Table ![![233, 0, 0], ![-94, 1, 0]] 
 ![![233, 0, 0], ![139, 1, 0], ![37, 0, 1]] where
  M :=![![![233, 0, 0], ![0, 233, 0], ![0, 0, 233]], ![![-94, 1, 0], ![-1, -93, 3], ![197, 20, -95]]]
  hmulB := by decide  
  f := ![![![7012, 652023, -21033], ![0, 1633563, 0]], ![![4183, 388926, -12546], ![1, 974406, 0]], ![![1126, 103540, -3340], ![31, 259407, 0]]]
  g := ![![![1, 0, 0], ![-139, 233, 0], ![-37, 0, 233]], ![![-1, 1, 0], ![55, -93, 3], ![4, 20, -95]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI233N1 : Nat.card (O ⧸ I233N1) = 233 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI233N1)

lemma isPrimeI233N1 : Ideal.IsPrime I233N1 := prime_ideal_of_norm_prime hp233.out _ NI233N1
def MulI233N0 : IdealMulLeCertificate' Table 
  ![![233, 0, 0], ![-104, -46, 1]] ![![233, 0, 0], ![-94, 1, 0]]
  ![![233, 0, 0]] where
 M := ![![![54289, 0, 0], ![-21902, 233, 0]], ![![-24232, -10718, 233], ![10019, 4194, -233]]]
 hmul := by decide  
 g := ![![![![233, 0, 0]], ![![-94, 1, 0]]], ![![![-104, -46, 1]], ![![43, 18, -1]]]]
 hle2 := by decide  


def PBC233 : ContainsPrimesAboveP 233 ![I233N0, I233N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI233N0
    exact isPrimeI233N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 233 (by decide) (𝕀 ⊙ MulI233N0)
instance hp239 : Fact (Nat.Prime 239) := {out := by norm_num}

def I239N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![239, 0, 0], ![-19, -80, 1]] i)))

def SI239N0: IdealEqSpanCertificate' Table ![![239, 0, 0], ![-19, -80, 1]] 
 ![![239, 0, 0], ![0, 239, 0], ![220, 159, 1]] where
  M :=![![![239, 0, 0], ![0, 239, 0], ![0, 0, 239]], ![![-19, -80, 1], ![277, -79, -241], ![-15898, -1541, 82]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-220, -159, 239]], ![![-1, -1, 1], ![223, 160, -241], ![-142, -61, 82]]]
  hle1 := by decide   
  hle2 := by decide  


def P239P0 : CertificateIrreducibleZModOfList' 239 2 2 7 [39, 71, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [168, 238], [0, 1]]
 g := ![![[106, 165], [220, 150], [194, 32], [158, 80], [66], [55, 50], [168, 1]], ![[102, 74], [86, 89], [73, 207], [214, 159], [66], [90, 189], [97, 238]]]
 h' := ![![[168, 238], [24, 72], [82, 110], [52, 157], [91, 124], [6, 122], [140, 222], [0, 1]], ![[0, 1], [170, 167], [159, 129], [138, 82], [130, 115], [187, 117], [152, 17], [168, 238]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [25]]
 b := ![[], [145, 132]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI239N0 : CertifiedPrimeIdeal' SI239N0 239 where
  n := 2
  hpos := by decide
  P := [39, 71, 1]
  hirr := P239P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3674, 858, 55]
  a := ![1, 1, -4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-66, -33, 55]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI239N0 : Ideal.IsPrime I239N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI239N0 B_one_repr
lemma NI239N0 : Nat.card (O ⧸ I239N0) = 57121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI239N0

def I239N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![239, 0, 0], ![2, 1, 0]] i)))

def SI239N1: IdealEqSpanCertificate' Table ![![239, 0, 0], ![2, 1, 0]] 
 ![![239, 0, 0], ![2, 1, 0], ![157, 0, 1]] where
  M :=![![![239, 0, 0], ![0, 239, 0], ![0, 0, 239]], ![![2, 1, 0], ![-1, 3, 3], ![197, 20, 1]]]
  hmulB := by decide  
  f := ![![![-20521, 61559, 61560], ![239, -4904280, 0]], ![![-171, 513, 513], ![1, -40869, 0]], ![![-13481, 40438, 40439], ![238, -3221640, 0]]]
  g := ![![![1, 0, 0], ![-2, 239, 0], ![-157, 0, 239]], ![![0, 1, 0], ![-2, 3, 3], ![0, 20, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI239N1 : Nat.card (O ⧸ I239N1) = 239 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI239N1)

lemma isPrimeI239N1 : Ideal.IsPrime I239N1 := prime_ideal_of_norm_prime hp239.out _ NI239N1
def MulI239N0 : IdealMulLeCertificate' Table 
  ![![239, 0, 0], ![-19, -80, 1]] ![![239, 0, 0], ![2, 1, 0]]
  ![![239, 0, 0]] where
 M := ![![![57121, 0, 0], ![478, 239, 0]], ![![-4541, -19120, 239], ![239, -239, -239]]]
 hmul := by decide  
 g := ![![![![239, 0, 0]], ![![2, 1, 0]]], ![![![-19, -80, 1]], ![![1, -1, -1]]]]
 hle2 := by decide  


def PBC239 : ContainsPrimesAboveP 239 ![I239N0, I239N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI239N0
    exact isPrimeI239N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 239 (by decide) (𝕀 ⊙ MulI239N0)
instance hp241 : Fact (Nat.Prime 241) := {out := by norm_num}

def I241N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31840, -1061, -583]] i)))

def SI241N0: IdealEqSpanCertificate' Table ![![31840, -1061, -583]] 
 ![![241, 0, 0], ![0, 241, 0], ![193, 63, 1]] where
  M :=![![![31840, -1061, -583], ![-113790, 19119, -2600], ![-128563, -55617, 20658]]]
  hmulB := by decide  
  f := ![![![-1038822, -225489, -57697]], ![![-11140820, -2418251, -618770]], ![![-3895533, -845573, -216361]]]
  g := ![![![599, 148, -583], ![1610, 759, -2600], ![-17077, -5631, 20658]]]
  hle1 := by decide   
  hle2 := by decide  


def P241P0 : CertificateIrreducibleZModOfList' 241 2 2 7 [220, 23, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [218, 240], [0, 1]]
 g := ![![[194, 161], [47], [211], [36], [220, 145], [34, 45], [218, 1]], ![[106, 80], [47], [211], [36], [18, 96], [204, 196], [195, 240]]]
 h' := ![![[218, 240], [184, 99], [99, 23], [27, 126], [41, 235], [232, 164], [240, 68], [0, 1]], ![[0, 1], [76, 142], [52, 218], [21, 115], [179, 6], [75, 77], [122, 173], [218, 240]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [57]]
 b := ![[], [147, 149]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI241N0 : CertifiedPrimeIdeal' SI241N0 241 where
  n := 2
  hpos := by decide
  P := [220, 23, 1]
  hirr := P241P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2293, 2910, 861]
  a := ![-2, 3, 6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-680, -213, 861]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI241N0 : Ideal.IsPrime I241N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI241N0 B_one_repr
lemma NI241N0 : Nat.card (O ⧸ I241N0) = 58081 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI241N0

def I241N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1038822, -225489, -57697]] i)))

def SI241N1: IdealEqSpanCertificate' Table ![![-1038822, -225489, -57697]] 
 ![![241, 0, 0], ![53, 1, 0], ![90, 0, 1]] where
  M :=![![![-1038822, -225489, -57697], ![-11140820, -2418251, -618770], ![-36459147, -7913903, -2024970]]]
  hmulB := by decide  
  f := ![![![31840, -1061, -583]], ![![6530, -154, -139]], ![![11357, -627, -132]]]
  g := ![![![66825, -225489, -57697], ![716663, -2418251, -618770], ![2345332, -7913903, -2024970]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI241N1 : Nat.card (O ⧸ I241N1) = 241 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI241N1)

lemma isPrimeI241N1 : Ideal.IsPrime I241N1 := prime_ideal_of_norm_prime hp241.out _ NI241N1
def MulI241N0 : IdealMulLeCertificate' Table 
  ![![31840, -1061, -583]] ![![-1038822, -225489, -57697]]
  ![![241, 0, 0]] where
 M := ![![![241, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC241 : ContainsPrimesAboveP 241 ![I241N0, I241N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI241N0
    exact isPrimeI241N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 241 (by decide) (𝕀 ⊙ MulI241N0)
instance hp251 : Fact (Nat.Prime 251) := {out := by norm_num}

def I251N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![251, 0, 0], ![40, 31, 1]] i)))

def SI251N0: IdealEqSpanCertificate' Table ![![251, 0, 0], ![40, 31, 1]] 
 ![![251, 0, 0], ![0, 251, 0], ![40, 31, 1]] where
  M :=![![![251, 0, 0], ![0, 251, 0], ![0, 0, 251]], ![![40, 31, 1], ![166, 91, 92], ![5969, 679, 30]]]
  hmulB := by decide  
  f := ![![![-39, -31, -1], ![251, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-40, -31, 251]], ![![0, 0, 1], ![-14, -11, 92], ![19, -1, 30]]]
  hle1 := by decide   
  hle2 := by decide  


def P251P0 : CertificateIrreducibleZModOfList' 251 2 2 7 [241, 97, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [154, 250], [0, 1]]
 g := ![![[166, 25], [174, 67], [20], [53, 114], [130, 9], [46, 105], [154, 1]], ![[0, 226], [201, 184], [20], [39, 137], [10, 242], [152, 146], [57, 250]]]
 h' := ![![[154, 250], [234, 5], [231, 103], [28, 32], [45, 37], [209, 3], [34, 132], [0, 1]], ![[0, 1], [0, 246], [29, 148], [187, 219], [221, 214], [169, 248], [31, 119], [154, 250]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [189]]
 b := ![[], [128, 220]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI251N0 : CertifiedPrimeIdeal' SI251N0 251 where
  n := 2
  hpos := by decide
  P := [241, 97, 1]
  hirr := P251P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![6616, 2015, 65]
  a := ![0, -5, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![16, 0, 65]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI251N0 : Ideal.IsPrime I251N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI251N0 B_one_repr
lemma NI251N0 : Nat.card (O ⧸ I251N0) = 63001 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI251N0

def I251N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![251, 0, 0], ![-92, 1, 0]] i)))

def SI251N1: IdealEqSpanCertificate' Table ![![251, 0, 0], ![-92, 1, 0]] 
 ![![251, 0, 0], ![159, 1, 0], ![221, 0, 1]] where
  M :=![![![251, 0, 0], ![0, 251, 0], ![0, 0, 251]], ![![-92, 1, 0], ![-1, -91, 3], ![197, 20, -93]]]
  hmulB := by decide  
  f := ![![![3211, 292110, -9630], ![0, 805710, 0]], ![![2034, 185003, -6099], ![1, 510283, 0]], ![![2869, 257196, -8479], ![114, 709410, 0]]]
  g := ![![![1, 0, 0], ![-159, 251, 0], ![-221, 0, 251]], ![![-1, 1, 0], ![55, -91, 3], ![70, 20, -93]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI251N1 : Nat.card (O ⧸ I251N1) = 251 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI251N1)

lemma isPrimeI251N1 : Ideal.IsPrime I251N1 := prime_ideal_of_norm_prime hp251.out _ NI251N1
def MulI251N0 : IdealMulLeCertificate' Table 
  ![![251, 0, 0], ![40, 31, 1]] ![![251, 0, 0], ![-92, 1, 0]]
  ![![251, 0, 0]] where
 M := ![![![63001, 0, 0], ![-23092, 251, 0]], ![![10040, 7781, 251], ![-3514, -2761, 0]]]
 hmul := by decide  
 g := ![![![![251, 0, 0]], ![![-92, 1, 0]]], ![![![40, 31, 1]], ![![-14, -11, 0]]]]
 hle2 := by decide  


def PBC251 : ContainsPrimesAboveP 251 ![I251N0, I251N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI251N0
    exact isPrimeI251N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 251 (by decide) (𝕀 ⊙ MulI251N0)
instance hp257 : Fact (Nat.Prime 257) := {out := by norm_num}

def I257N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![257, 0, 0], ![100, 1, 0]] i)))

def SI257N0: IdealEqSpanCertificate' Table ![![257, 0, 0], ![100, 1, 0]] 
 ![![257, 0, 0], ![100, 1, 0], ![231, 0, 1]] where
  M :=![![![257, 0, 0], ![0, 257, 0], ![0, 0, 257]], ![![100, 1, 0], ![-1, 101, 3], ![197, 20, 99]]]
  hmulB := by decide  
  f := ![![![-1071, 98171, 2916], ![257, -249804, 0]], ![![-478, 38177, 1134], ![258, -97146, 0]], ![![-893, 88240, 2621], ![52, -224532, 0]]]
  g := ![![![1, 0, 0], ![-100, 257, 0], ![-231, 0, 257]], ![![0, 1, 0], ![-42, 101, 3], ![-96, 20, 99]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI257N0 : Nat.card (O ⧸ I257N0) = 257 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI257N0)

lemma isPrimeI257N0 : Ideal.IsPrime I257N0 := prime_ideal_of_norm_prime hp257.out _ NI257N0

def I257N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-233, -11, 10]] i)))

def SI257N1: IdealEqSpanCertificate' Table ![![-233, -11, 10]] 
 ![![257, 0, 0], ![179, 1, 0], ![225, 0, 1]] where
  M :=![![![-233, -11, 10], ![1981, -44, -43], ![-3547, 370, -12]]]
  hmulB := by decide  
  f := ![![![-16438, -3568, -913]], ![![-12135, -2634, -674]], ![![-16636, -3611, -924]]]
  g := ![![![-2, -11, 10], ![76, -44, -43], ![-261, 370, -12]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI257N1 : Nat.card (O ⧸ I257N1) = 257 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI257N1)

lemma isPrimeI257N1 : Ideal.IsPrime I257N1 := prime_ideal_of_norm_prime hp257.out _ NI257N1

def I257N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![257, 0, 0], ![-22, 1, 0]] i)))

def SI257N2: IdealEqSpanCertificate' Table ![![257, 0, 0], ![-22, 1, 0]] 
 ![![257, 0, 0], ![235, 1, 0], ![17, 0, 1]] where
  M :=![![![257, 0, 0], ![0, 257, 0], ![0, 0, 257]], ![![-22, 1, 0], ![-1, -21, 3], ![197, 20, -23]]]
  hmulB := by decide  
  f := ![![![-7047, -148471, 21210], ![257, -1816990, 0]], ![![-6441, -135745, 19392], ![258, -1661248, 0]], ![![-467, -9821, 1403], ![7, -120190, 0]]]
  g := ![![![1, 0, 0], ![-235, 257, 0], ![-17, 0, 257]], ![![-1, 1, 0], ![19, -21, 3], ![-16, 20, -23]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI257N2 : Nat.card (O ⧸ I257N2) = 257 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI257N2)

lemma isPrimeI257N2 : Ideal.IsPrime I257N2 := prime_ideal_of_norm_prime hp257.out _ NI257N2
def MulI257N0 : IdealMulLeCertificate' Table 
  ![![257, 0, 0], ![100, 1, 0]] ![![-233, -11, 10]]
  ![![257, 0, 0], ![-116, -78, 1]] where
 M := ![![![-59881, -2827, 2570]], ![![-21319, -1144, 957]]]
 hmul := by decide  
 g := ![![![![-117, 67, 9], ![257, 0, 0]]], ![![![1, 52, 3], ![186, 0, 0]]]]
 hle2 := by decide  

def MulI257N1 : IdealMulLeCertificate' Table 
  ![![257, 0, 0], ![-116, -78, 1]] ![![257, 0, 0], ![-22, 1, 0]]
  ![![257, 0, 0]] where
 M := ![![![66049, 0, 0], ![-5654, 257, 0]], ![![-29812, -20046, 257], ![2827, 1542, -257]]]
 hmul := by decide  
 g := ![![![![257, 0, 0]], ![![-22, 1, 0]]], ![![![-116, -78, 1]], ![![11, 6, -1]]]]
 hle2 := by decide  


def PBC257 : ContainsPrimesAboveP 257 ![I257N0, I257N1, I257N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI257N0
    exact isPrimeI257N1
    exact isPrimeI257N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 257 (by decide) (𝕀 ⊙ MulI257N0 ⊙ MulI257N1)


lemma PB276I4_primes (p : ℕ) :
  p ∈ Set.range ![197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257] ↔ Nat.Prime p ∧ 193 < p ∧ p ≤ 257 := by
  rw [← List.mem_ofFn']
  convert primes_range 193 257 (by omega)

def PB276I4 : PrimesBelowBoundCertificateInterval O 193 257 276 where
  m := 11
  g := ![2, 2, 2, 3, 2, 1, 2, 2, 2, 2, 3]
  P := ![197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257]
  hP := PB276I4_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I197N0, I197N1]
    · exact ![I199N0, I199N1]
    · exact ![I211N0, I211N1]
    · exact ![I223N0, I223N1, I223N2]
    · exact ![I227N0, I227N1]
    · exact ![I229N0]
    · exact ![I233N0, I233N1]
    · exact ![I239N0, I239N1]
    · exact ![I241N0, I241N1]
    · exact ![I251N0, I251N1]
    · exact ![I257N0, I257N1, I257N2]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC197
    · exact PBC199
    · exact PBC211
    · exact PBC223
    · exact PBC227
    · exact PBC229
    · exact PBC233
    · exact PBC239
    · exact PBC241
    · exact PBC251
    · exact PBC257
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![38809, 197]
    · exact ![39601, 199]
    · exact ![44521, 211]
    · exact ![223, 223, 223]
    · exact ![51529, 227]
    · exact ![12008989]
    · exact ![54289, 233]
    · exact ![57121, 239]
    · exact ![58081, 241]
    · exact ![63001, 251]
    · exact ![257, 257, 257]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI197N0
      exact NI197N1
    · dsimp ; intro j
      fin_cases j
      exact NI199N0
      exact NI199N1
    · dsimp ; intro j
      fin_cases j
      exact NI211N0
      exact NI211N1
    · dsimp ; intro j
      fin_cases j
      exact NI223N0
      exact NI223N1
      exact NI223N2
    · dsimp ; intro j
      fin_cases j
      exact NI227N0
      exact NI227N1
    · dsimp ; intro j
      fin_cases j
      exact NI229N0
    · dsimp ; intro j
      fin_cases j
      exact NI233N0
      exact NI233N1
    · dsimp ; intro j
      fin_cases j
      exact NI239N0
      exact NI239N1
    · dsimp ; intro j
      fin_cases j
      exact NI241N0
      exact NI241N1
    · dsimp ; intro j
      fin_cases j
      exact NI251N0
      exact NI251N1
    · dsimp ; intro j
      fin_cases j
      exact NI257N0
      exact NI257N1
      exact NI257N2
  β := ![I197N1, I199N1, I211N1, I223N0, I223N1, I223N2, I227N1, I233N1, I239N1, I241N1, I251N1, I257N0, I257N1, I257N2]
  Il := ![[I197N1], [I199N1], [I211N1], [I223N0, I223N1, I223N2], [I227N1], [], [I233N1], [I239N1], [I241N1], [I251N1], [I257N0, I257N1, I257N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
