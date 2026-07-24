
import IdealArithmetic.Examples.NF3_1_664563_1.RI3_1_664563_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp2 : Fact (Nat.Prime 2) := {out := by norm_num}

def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19263002744859815392567, 1035007752957876050295, 651305680205257466697]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![19263002744859815392567, 1035007752957876050295, 651305680205257466697]] 
 ![![2, 0, 0], ![0, 2, 0], ![1, 1, 1]] where
  M :=![![![19263002744859815392567, 1035007752957876050295, 651305680205257466697], ![91834100908941302804277, 4934277780344151125233, 3105023258873628150885], ![145936093167060523091595, 7841196404573827828269, 4934277780344151125233]]]
  hmulB := by decide  
  f := ![![![69124468112, -14924468121, 267447837]], ![![37710145017, 63240615698, -44773404363]], ![![-998757695966, 194612247289, 9367329586]]]
  g := ![![![9305848532327278962935, 191851036376309291799, 651305680205257466697], ![44364538825033837326696, 914627260735261487174, 3105023258873628150885], ![70500907693358185983181, 1453459312114838351518, 4934277780344151125233]]]
  hle1 := by decide   
  hle2 := by decide  


def P2P0 : CertificateIrreducibleZModOfList' 2 2 2 1 [1, 1, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![0, 1]
 hbits := by decide
 h := ![[0, 1], [1, 1], [0, 1]]
 g := ![![[1]], ![[1]]]
 h' := ![![[1, 1], [0, 1]], ![[0, 1], [1, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], []]
 b := ![[], [1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI2N0 : CertifiedPrimeIdeal' SI2N0 2 where
  n := 2
  hpos := by decide
  P := [1, 1, 1]
  hirr := P2P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1691, 689, -189]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-751, 439, -189]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI2N0 B_one_repr
lemma NI2N0 : Nat.card (O ⧸ I2N0) = 4 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![69124468112, -14924468121, 267447837]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![69124468112, -14924468121, 267447837]] 
 ![![2, 0, 0], ![1, 1, 0], ![1, 0, 1]] where
  M :=![![![69124468112, -14924468121, 267447837], ![37710145017, 63240615698, -44773404363], ![-2104350005061, 340908347001, 63240615698]]]
  hmulB := by decide  
  f := ![![![19263002744859815392567, 1035007752957876050295, 651305680205257466697]], ![![55548551826900559098422, 2984642766651013587764, 1878164469539442808791]], ![![82599547955960169242081, 4438102078765851939282, 2792791730274704295965]]]
  g := ![![![41890744198, -14924468121, 267447837], ![9621466841, 63240615698, -44773404363], ![-1254249483880, 340908347001, 63240615698]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N1 : Nat.card (O ⧸ I2N1) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N1)

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := prime_ideal_of_norm_prime hp2.out _ NI2N1
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![19263002744859815392567, 1035007752957876050295, 651305680205257466697]] ![![69124468112, -14924468121, 267447837]]
  ![![2, 0, 0]] where
 M := ![![![2, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC2 : ContainsPrimesAboveP 2 ![I2N0, I2N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI2N0
    exact isPrimeI2N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 2 (by decide) (𝕀 ⊙ MulI2N0)

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![199940283, -13733424, -17749232]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![199940283, -13733424, -17749232]] 
 ![![3, 0, 0], ![0, 1, 0], ![0, 0, 1]] where
  M :=![![![199940283, -13733424, -17749232], ![-2502641712, 590423387, -41200272], ![-1936412784, -532078576, 590423387]]]
  hmulB := by decide  
  f := ![![![326677993859979097, 17552520800840720, 11045382478380112]], ![![519132976483865264, 27893193111872211, 17552520800840720]], ![![824968477639513840, 44325839621789808, 27893193111872211]]]
  g := ![![![66646761, -13733424, -17749232], ![-834213904, 590423387, -41200272], ![-645470928, -532078576, 590423387]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N0 : Nat.card (O ⧸ I3N0) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N0)

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := prime_ideal_of_norm_prime hp3.out _ NI3N0

def I3N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-464772127, -24972366, -15714514]] i)))

def SI3N1: IdealEqSpanCertificate' Table ![![-464772127, -24972366, -15714514]] 
 ![![3, 0, 0], ![0, 1, 0], ![1, 0, 1]] where
  M :=![![![-464772127, -24972366, -15714514], ![-2215746474, -119052819, -74917098], ![-3521103606, -189190106, -119052819]]]
  hmulB := by decide  
  f := ![![![-14373, 1270, 1098]], ![![51606, -12843, 1270]], ![![54899, 8312, -12477]]]
  g := ![![![-149685871, -24972366, -15714514], ![-713609792, -119052819, -74917098], ![-1134016929, -189190106, -119052819]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N1 : Nat.card (O ⧸ I3N1) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N1)

lemma isPrimeI3N1 : Ideal.IsPrime I3N1 := prime_ideal_of_norm_prime hp3.out _ NI3N1
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![199940283, -13733424, -17749232]] ![![-464772127, -24972366, -15714514]]
  ![![-14373, 1270, 1098]] where
 M := ![![![-14373, 1270, 1098]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI3N1 : IdealMulLeCertificate' Table 
  ![![-14373, 1270, 1098]] ![![-464772127, -24972366, -15714514]]
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

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-89016050050332896902835189017, -4782862939910325215175236474, -3009741513050863140748490568]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![-89016050050332896902835189017, -4782862939910325215175236474, -3009741513050863140748490568]] 
 ![![5, 0, 0], ![0, 5, 0], ![4, 3, 1]] where
  M :=![![![-89016050050332896902835189017, -4782862939910325215175236474, -3009741513050863140748490568], ![-424373553340171702845537170088, -22801736763213907806368396521, -14348588819730975645525709422], ![-674383674527355855339708342834, -36234866435363412881323854268, -22801736763213907806368396521]]]
  hmulB := by decide  
  f := ![![![-116193328478069, 31954673872546, -4771241468820]], ![![-672745047103620, -11226016164029, 95864021617638]], ![![404520112161170, -166622105446491, 51456216562721]]]
  g := ![![![-15395416799625888867968245349, 849272319848452841414047046, -3009741513050863140748490568], ![-73395839612249560052686866480, 4048805939195803826041746349, -14348588819730975645525709422], ![-116635345494900044822846951350, 6434068770855662107556267059, -22801736763213907806368396521]]]
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
  c := ![3752, -36, 108]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![664, -72, 108]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI5N0 B_one_repr
lemma NI5N0 : Nat.card (O ⧸ I5N0) = 25 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI5N0

def I5N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![116193328478069, -31954673872546, 4771241468820]] i)))

def SI5N1: IdealEqSpanCertificate' Table ![![116193328478069, -31954673872546, 4771241468820]] 
 ![![5, 0, 0], ![1, 1, 0], ![3, 0, 1]] where
  M :=![![![116193328478069, -31954673872546, 4771241468820], ![672745047103620, 11226016164029, -95864021617638], ![-4505609016028986, 927251174230552, 11226016164029]]]
  hmulB := by decide  
  f := ![![![89016050050332896902835189017, 4782862939910325215175236474, 3009741513050863140748490568]], ![![102677920678100919949674471821, 5516919940624846604308726599, 3471666066556367757254839998]], ![![188286364935670909209642781977, 10116691051018877705369912738, 6366192260473299445722773645]]]
  g := ![![![26766855588831, -31954673872546, 4771241468820], ![189822219158501, 11226016164029, -95864021617638], ![-1093307647750325, 927251174230552, 11226016164029]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N1 : Nat.card (O ⧸ I5N1) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N1)

lemma isPrimeI5N1 : Ideal.IsPrime I5N1 := prime_ideal_of_norm_prime hp5.out _ NI5N1
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![-89016050050332896902835189017, -4782862939910325215175236474, -3009741513050863140748490568]] ![![116193328478069, -31954673872546, 4771241468820]]
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
instance hp7 : Fact (Nat.Prime 7) := {out := by norm_num}

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1458244046456, 1049697102652, -468066734533]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![-1458244046456, 1049697102652, -468066734533]] 
 ![![7, 0, 0], ![0, 7, 0], ![6, 2, 1]] where
  M :=![![![-1458244046456, 1049697102652, -468066734533], ![-65997409569153, 8839224113270, 3149091307956], ![148007291473932, -45092472781395, 8839224113270]]]
  hmulB := by decide  
  f := ![![![31447456716392475371767360, 1689682649344932677288785, 1063276969778807384121746]], ![![149922052738811841161166186, 8055363381258712921088948, 5069047948034798031866355]], ![![103824871333373434578665031, 5578545993228921437039914, 3510445870857307612793162]]]
  g := ![![![192879480106, 283690081674, -468066734533], ![-12127422488127, 363005928194, 3149091307956], ![13567420970616, -8967274429705, 8839224113270]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P0 : CertificateIrreducibleZModOfList' 7 2 2 2 [4, 1, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [6, 6], [0, 1]]
 g := ![![[2, 2], [6, 1]], ![[0, 5], [5, 6]]]
 h' := ![![[6, 6], [4, 4], [0, 1]], ![[0, 1], [0, 3], [6, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4]]
 b := ![[], [1, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N0 : CertifiedPrimeIdeal' SI7N0 7 where
  n := 2
  hpos := by decide
  P := [4, 1, 1]
  hirr := P7P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![286, 2, -20]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![58, 6, -20]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N0 B_one_repr
lemma NI7N0 : Nat.card (O ⧸ I7N0) = 49 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N0

def I7N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-31447456716392475371767360, -1689682649344932677288785, -1063276969778807384121746]] i)))

def SI7N1: IdealEqSpanCertificate' Table ![![-31447456716392475371767360, -1689682649344932677288785, -1063276969778807384121746]] 
 ![![7, 0, 0], ![1, 1, 0], ![2, 0, 1]] where
  M :=![![![-31447456716392475371767360, -1689682649344932677288785, -1063276969778807384121746], ![-149922052738811841161166186, -8055363381258712921088948, -5069047948034798031866355], ![-238245253557635507497718685, -12800999294015428153368792, -8055363381258712921088948]]]
  hmulB := by decide  
  f := ![![![1458244046456, -1049697102652, 468066734533]], ![![9636521945087, -1412703030846, -383003510489]], ![![-20727257625860, 6141868368013, -1129012949172]]]
  g := ![![![-3947317161069989703747869, -1689682649344932677288785, -1063276969778807384121746], ![-18818370494497647453763504, -8055363381258712921088948, -5069047948034798031866355], ![-29904789643014664786024571, -12800999294015428153368792, -8055363381258712921088948]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N1 : Nat.card (O ⧸ I7N1) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N1)

lemma isPrimeI7N1 : Ideal.IsPrime I7N1 := prime_ideal_of_norm_prime hp7.out _ NI7N1
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![-1458244046456, 1049697102652, -468066734533]] ![![-31447456716392475371767360, -1689682649344932677288785, -1063276969778807384121746]]
  ![![7, 0, 0]] where
 M := ![![![-7, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC7 : ContainsPrimesAboveP 7 ![I7N0, I7N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI7N0
    exact isPrimeI7N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 7 (by decide) (𝕀 ⊙ MulI7N0)
instance hp11 : Fact (Nat.Prime 11) := {out := by norm_num}

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2362502051720924, 171747466910711, 203764597602752]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![-2362502051720924, 171747466910711, 203764597602752]] 
 ![![11, 0, 0], ![0, 11, 0], ![3, 1, 1]] where
  M :=![![![-2362502051720924, 171747466910711, 203764597602752], ![28730808261988032, -6845323198981468, 515242400732133], ![24216392834410251, 5798491815293702, -6845323198981468]]]
  hmulB := by decide  
  f := ![![![3988256441361484328216489409878, 214290388277851291740700288332, 134847827661089017805364852409]], ![![19013543700213551510556444189669, 1021604232817525936498462656880, 642871164833553875222100864996]], ![![5563023433770457875513150279465, 298903159600866839116118658345, 188092625512213351376059825373]]]
  g := ![![![-270345076775380, -2910648244731, 203764597602752], ![2471371005435603, -669142327246691, 515242400732133], ![4068396584668605, 1149437728570470, -6845323198981468]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P0 : CertificateIrreducibleZModOfList' 11 2 2 3 [3, 3, 1] where
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
 g := ![![[1, 4], [2, 9], [1]], ![[0, 7], [8, 2], [1]]]
 h' := ![![[8, 10], [5, 9], [8, 8], [0, 1]], ![[0, 1], [0, 2], [6, 3], [8, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5]]
 b := ![[], [1, 8]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 2
  hpos := by decide
  P := [3, 3, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5365, -694, 1066]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![197, -160, 1066]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N0 B_one_repr
lemma NI11N0 : Nat.card (O ⧸ I11N0) = 121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N0

def I11N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3988256441361484328216489409878, 214290388277851291740700288332, 134847827661089017805364852409]] i)))

def SI11N1: IdealEqSpanCertificate' Table ![![3988256441361484328216489409878, 214290388277851291740700288332, 134847827661089017805364852409]] 
 ![![11, 0, 0], ![8, 1, 0], ![8, 0, 1]] where
  M :=![![![3988256441361484328216489409878, 214290388277851291740700288332, 134847827661089017805364852409], ![19013543700213551510556444189669, 1021604232817525936498462656880, 642871164833553875222100864996], ![30214944747177032135438740654812, 1623459357958455418556741719919, 1021604232817525936498462656880]]]
  hmulB := by decide  
  f := ![![![-2362502051720924, 171747466910711, 203764597602752]], ![![893708349838240, -497394860335980, 195032652868559]], ![![483306947331169, 652042868234490, -474109674378132]]]
  g := ![![![108650064895451077440724389450, 214290388277851291740700288332, 134847827661089017805364852409], ![517976410818628456071994183151, 1021604232817525936498462656880, 642871164833553875222100864996], ![823130547360834663181555058220, 1623459357958455418556741719919, 1021604232817525936498462656880]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N1 : Nat.card (O ⧸ I11N1) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N1)

lemma isPrimeI11N1 : Ideal.IsPrime I11N1 := prime_ideal_of_norm_prime hp11.out _ NI11N1
def MulI11N0 : IdealMulLeCertificate' Table 
  ![![-2362502051720924, 171747466910711, 203764597602752]] ![![3988256441361484328216489409878, 214290388277851291740700288332, 134847827661089017805364852409]]
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

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![13, 0, 0]] 
 ![![13, 0, 0], ![0, 13, 0], ![0, 0, 13]] where
  M :=![![![13, 0, 0], ![0, 13, 0], ![0, 0, 13]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P0 : CertificateIrreducibleZModOfList' 13 3 2 3 [8, 0, 11, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [5, 10, 8], [10, 2, 5], [0, 1]]
 g := ![![[1, 2, 9], [8, 4], [1]], ![[3, 0, 3, 6], [5, 3], [3, 5, 6, 5]], ![[6, 4, 1, 8], [12, 10], [7, 11, 10, 8]]]
 h' := ![![[5, 10, 8], [0, 7, 10], [5, 0, 2], [0, 1]], ![[10, 2, 5], [8, 6, 11], [10, 8, 4], [5, 10, 8]], ![[0, 1], [7, 0, 5], [8, 5, 7], [10, 2, 5]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11, 4], []]
 b := ![[], [6, 1, 6], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 3
  hpos := by decide
  P := [8, 0, 11, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-29874, 2210, 2626]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2298, 170, 202]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N0 B_one_repr
lemma NI13N0 : Nat.card (O ⧸ I13N0) = 2197 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N0

def PBC13 : ContainsPrimesAboveP 13 ![I13N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI13N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![13, 0, 0]]) timesTableT_eq_Table B_one_repr 13 (by decide) 𝕀

instance hp17 : Fact (Nat.Prime 17) := {out := by norm_num}

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 0, 0]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![17, 0, 0]] 
 ![![17, 0, 0], ![0, 17, 0], ![0, 0, 17]] where
  M :=![![![17, 0, 0], ![0, 17, 0], ![0, 0, 17]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P0 : CertificateIrreducibleZModOfList' 17 3 2 4 [11, 0, 3, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [13, 8, 15], [1, 8, 2], [0, 1]]
 g := ![![[5, 13, 4], [1, 13], [14, 1], []], ![[15, 6, 5, 1], [6, 13], [1, 13], [7, 4]], ![[14, 11, 14, 1], [14, 1], [6, 13], [3, 4]]]
 h' := ![![[13, 8, 15], [7, 15, 15], [16, 6, 9], [0, 0, 1], [0, 1]], ![[1, 8, 2], [1, 13, 5], [4, 11, 9], [7, 11, 8], [13, 8, 15]], ![[0, 1], [1, 6, 14], [6, 0, 16], [2, 6, 8], [1, 8, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [16, 16], []]
 b := ![[], [14, 9, 8], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 3
  hpos := by decide
  P := [11, 0, 3, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![17918, -9656, 4913]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1054, -568, 289]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N0 B_one_repr
lemma NI17N0 : Nat.card (O ⧸ I17N0) = 4913 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N0

def PBC17 : ContainsPrimesAboveP 17 ![I17N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI17N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![17, 0, 0]]) timesTableT_eq_Table B_one_repr 17 (by decide) 𝕀


def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-8627111733545244110421378784, 1750423738402287706425300275, 37245664589842861534474410]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![-8627111733545244110421378784, 1750423738402287706425300275, 37245664589842861534474410]] 
 ![![19, 0, 0], ![8, 1, 0], ![4, 0, 1]] where
  M :=![![![-8627111733545244110421378784, 1750423738402287706425300275, 37245664589842861534474410], ![5251638707167843476360891810, -9446516354521787064179815804, 5251271215206863119275900825], ![246809747114722566605967338775, -36758776009127715049236308780, -9446516354521787064179815804]]]
  hmulB := by decide  
  f := ![![![-282266973599216575749222061179335281663619350667724909916, -15166301430191243677751059839973521483717507269122226300, -9543791571569705237235360825975023442045670301496802515]], ![![-189674231599213739181261177152482134665126016729097285997, -10191261603484895260634347459351207253071298009882792894, -6413117729638493312165056111985302736185151801017952580]], ![![-171974547160727982187357246429137245045191890927217555156, -9240251480017566313186467457963300793117440701376297095, -5814669753208520077841345595357097879305120275830656034]]]
  g := ![![![-1198920226269627221471667296, 1750423738402287706425300275, 37245664589842861534474410], ![3148351825395509869089253418, -9446516354521787064179815804, 5251271215206863119275900825], ![30456106347675338697714582749, -36758776009127715049236308780, -9446516354521787064179815804]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N0 : Nat.card (O ⧸ I19N0) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N0)

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := prime_ideal_of_norm_prime hp19.out _ NI19N0

def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13661870627768023046839282804, 734057000714521389133490125, 461924553505504616506349430]] i)))

def SI19N1: IdealEqSpanCertificate' Table ![![13661870627768023046839282804, 734057000714521389133490125, 461924553505504616506349430]] 
 ![![19, 0, 0], ![15, 1, 0], ![1, 0, 1]] where
  M :=![![![13661870627768023046839282804, 734057000714521389133490125, 461924553505504616506349430], ![65131362044276150927395269630, 3499530450646921483699595344, 2202171002143564167400470375], ![103502037100747515867822107625, 5561199999039246414861640460, 3499530450646921483699595344]]]
  hmulB := by decide  
  f := ![![![-259598784894164, 41274865959800, 8292752492955]], ![![-143405456416095, 9320192087254, 13063993961775]], ![![292639858707244, -25105937788785, -22828767749801]]]
  g := ![![![115215319133931452280556921, 734057000714521389133490125, 461924553505504616506349430], ![549275488548882342342151005, 3499530450646921483699595344, 2202171002143564167400470375], ![872868771816415692694626599, 5561199999039246414861640460, 3499530450646921483699595344]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N1 : Nat.card (O ⧸ I19N1) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N1)

lemma isPrimeI19N1 : Ideal.IsPrime I19N1 := prime_ideal_of_norm_prime hp19.out _ NI19N1
def MulI19N0 : IdealMulLeCertificate' Table 
  ![![-8627111733545244110421378784, 1750423738402287706425300275, 37245664589842861534474410]] ![![13661870627768023046839282804, 734057000714521389133490125, 461924553505504616506349430]]
  ![![259598784894164, -41274865959800, -8292752492955]] where
 M := ![![![259598784894164, -41274865959800, -8292752492955]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI19N1 : IdealMulLeCertificate' Table 
  ![![259598784894164, -41274865959800, -8292752492955]] ![![13661870627768023046839282804, 734057000714521389133490125, 461924553505504616506349430]]
  ![![19, 0, 0]] where
 M := ![![![-19, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC19 : ContainsPrimesAboveP 19 ![I19N0, I19N1, I19N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI19N0
    exact isPrimeI19N1
    exact isPrimeI19N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 19 (by decide) (𝕀 ⊙ MulI19N0 ⊙ MulI19N1)
instance hp23 : Fact (Nat.Prime 23) := {out := by norm_num}

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4305611445289308662, -881850860873601176, 1123251845897777987]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![-4305611445289308662, -881850860873601176, 1123251845897777987]] 
 ![![23, 0, 0], ![0, 23, 0], ![11, 21, 1]] where
  M :=![![![-4305611445289308662, -881850860873601176, 1123251845897777987], ![158378510271586696167, -29017152055040424376, -2645552582620803528], ![-124340971383177765816, 72193555696414791261, -29017152055040424376]]]
  hmulB := by decide  
  f := ![![![44912476569850682469303087163408146008, 2413162790351494588978829832083178497, 1518545757869182307946838448871163480]], ![![214114951859554705420504221290834050680, 11504469896728671694472641288242549448, 7239488371054483766936489496249535491]], ![![231769877598198567740823374444727514715, 12453075119882053633854771565092315587, 7836423001105818964676267115089808393]]]
  g := ![![![-724407902181081153, -1063919114118562561, 1123251845897777987], ![8151286464365892825, 1153889225217236944, -2645552582620803528], ![8471639183576821840, 29632771689228856659, -29017152055040424376]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P0 : CertificateIrreducibleZModOfList' 23 2 2 4 [8, 7, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [16, 22], [0, 1]]
 g := ![![[21, 3], [9, 1], [22, 3], [1]], ![[0, 20], [2, 22], [1, 20], [1]]]
 h' := ![![[16, 22], [20, 16], [8, 1], [15, 16], [0, 1]], ![[0, 1], [0, 7], [1, 22], [18, 7], [16, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [16]]
 b := ![[], [5, 8]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 2
  hpos := by decide
  P := [8, 7, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5614, 958, 234]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-356, -172, 234]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N0 B_one_repr
lemma NI23N0 : Nat.card (O ⧸ I23N0) = 529 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N0

def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2164227223363137015538809486843005024, 617591164499090343480543213966930542, -102965716368287854718853415852598113]] i)))

def SI23N1: IdealEqSpanCertificate' Table ![![-2164227223363137015538809486843005024, 617591164499090343480543213966930542, -102965716368287854718853415852598113]] 
 ![![23, 0, 0], ![6, 1, 0], ![11, 0, 1]] where
  M :=![![![-2164227223363137015538809486843005024, 617591164499090343480543213966930542, -102965716368287854718853415852598113], ![-14518166007928587515358331635216333933, 101018536739195788275965661914153462, 1852773493497271030441629641900791626], ![87080354194371738430756593169337206422, -18426394288289516728358061252344583235, 101018536739195788275965661914153462]]]
  hmulB := by decide  
  f := ![![![-34150139662837257228387802577697966431506811141957742020702955395634575554, -1834898732237503660362926917592041441061705500489711493466311446449599151, -1154657985403854905561659786783206523959233482110748049801508634850858498]], ![![-15987287561694221089326993278374779063795338601276605528096976082077326154, -859002451190324837748210816261724850033648153846067560255114526417968848, -540549743875462626715597368411972324649587712788418381704695049932780367]], ![![-27581402501595558505366892336311107562446756440460194904629670578320600495, -1481958228668201752061122342839054381495878832774710083153977388132380815, -932560948843254489878675866220986724693706210379978846647233061403266612]]]
  g := ![![![-205963101317674464109333965055043871, 617591164499090343480543213966930542, -102965716368287854718853415852598113], ![-1543686332905814938255306594243911417, 101018536739195788275965661914153462, 1852773493497271030441629641900791626], ![8544674609564247179559536452276044250, -18426394288289516728358061252344583235, 101018536739195788275965661914153462]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N1 : Nat.card (O ⧸ I23N1) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N1)

lemma isPrimeI23N1 : Ideal.IsPrime I23N1 := prime_ideal_of_norm_prime hp23.out _ NI23N1
def MulI23N0 : IdealMulLeCertificate' Table 
  ![![-4305611445289308662, -881850860873601176, 1123251845897777987]] ![![-2164227223363137015538809486843005024, 617591164499090343480543213966930542, -102965716368287854718853415852598113]]
  ![![23, 0, 0]] where
 M := ![![![119934347285777071328430666697858320117227436681576855610, -23445672267525959593631176730491362205664143314872874061, -1077070275514450901101899683745398088118192113585356376]]]
 hmul := by decide  
 g := ![![![![5214536838512046579496985508602535657270758116590298070, -1019377055109824330157877249151798356768006231081429307, -46829142413671778308778247119365134266008352764580712]]]]
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


def P29P0 : CertificateIrreducibleZModOfList' 29 3 2 4 [15, 17, 5, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [25, 21, 23], [28, 7, 6], [0, 1]]
 g := ![![[8, 23, 4], [9, 13], [21, 16, 25], [1]], ![[20, 20, 3, 25], [26, 24], [6, 18, 25, 7], [27, 22, 13, 16]], ![[26, 6, 16, 5], [0, 7], [15, 11, 19, 9], [20, 27, 24, 13]]]
 h' := ![![[25, 21, 23], [26, 11, 27], [4, 5, 19], [14, 12, 24], [0, 1]], ![[28, 7, 6], [11, 9, 7], [13, 10, 16], [24, 16, 9], [25, 21, 23]], ![[0, 1], [4, 9, 24], [2, 14, 23], [18, 1, 25], [28, 7, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1, 26], []]
 b := ![[], [18, 25, 14], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 3
  hpos := by decide
  P := [15, 17, 5, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![6380, 319, -319]
  a := ![13, -1, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![220, 11, -11]
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

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2569, 3180, -1662]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![-2569, 3180, -1662]] 
 ![![31, 0, 0], ![0, 31, 0], ![21, 17, 1]] where
  M :=![![![-2569, 3180, -1662], ![-234342, 33995, 9540], ![448380, -148074, 33995]]]
  hmulB := by decide  
  f := ![![![-82847935, -4451448, -2801190]], ![![-394967790, -21221755, -13354344]], ![![-292964943, -15741107, -9905503]]]
  g := ![![![1043, 1014, -1662], ![-14022, -4135, 9540], ![-8565, -23419, 33995]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P0 : CertificateIrreducibleZModOfList' 31 2 2 4 [17, 30, 1] where
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
 g := ![![[20, 4], [13, 2], [25, 8], [1, 1]], ![[24, 27], [15, 29], [2, 23], [2, 30]]]
 h' := ![![[1, 30], [27, 29], [9, 23], [14, 15], [0, 1]], ![[0, 1], [25, 2], [1, 8], [29, 16], [1, 30]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7]]
 b := ![[], [6, 19]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 2
  hpos := by decide
  P := [17, 30, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1176, -257, -6]
  a := ![1, -4, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![42, -5, -6]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N0 B_one_repr
lemma NI31N0 : Nat.card (O ⧸ I31N0) = 961 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N0

def I31N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![82847935, 4451448, 2801190]] i)))

def SI31N1: IdealEqSpanCertificate' Table ![![82847935, 4451448, 2801190]] 
 ![![31, 0, 0], ![11, 1, 0], ![1, 0, 1]] where
  M :=![![![82847935, 4451448, 2801190], ![394967790, 21221755, 13354344], ![627654168, 33724074, 21221755]]]
  hmulB := by decide  
  f := ![![![2569, -3180, 1662]], ![![8471, -2225, 282]], ![![-14381, 4674, -1043]]]
  g := ![![![1002607, 4451448, 2801190], ![4779811, 21221755, 13354344], ![7595729, 33724074, 21221755]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N1 : Nat.card (O ⧸ I31N1) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N1)

lemma isPrimeI31N1 : Ideal.IsPrime I31N1 := prime_ideal_of_norm_prime hp31.out _ NI31N1
def MulI31N0 : IdealMulLeCertificate' Table 
  ![![-2569, 3180, -1662]] ![![82847935, 4451448, 2801190]]
  ![![31, 0, 0]] where
 M := ![![![-31, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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


lemma PB231I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 31 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 31 (by omega)

def PB231I0 : PrimesBelowBoundCertificateInterval O 1 31 231 where
  m := 11
  g := ![2, 3, 2, 2, 2, 1, 1, 3, 2, 1, 2]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]
  hP := PB231I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N1]
    · exact ![I3N0, I3N1, I3N1]
    · exact ![I5N0, I5N1]
    · exact ![I7N0, I7N1]
    · exact ![I11N0, I11N1]
    · exact ![I13N0]
    · exact ![I17N0]
    · exact ![I19N0, I19N1, I19N1]
    · exact ![I23N0, I23N1]
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
    · exact ![4, 2]
    · exact ![3, 3, 3]
    · exact ![25, 5]
    · exact ![49, 7]
    · exact ![121, 11]
    · exact ![2197]
    · exact ![4913]
    · exact ![19, 19, 19]
    · exact ![529, 23]
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
      exact NI7N1
    · dsimp ; intro j
      fin_cases j
      exact NI11N0
      exact NI11N1
    · dsimp ; intro j
      fin_cases j
      exact NI13N0
    · dsimp ; intro j
      fin_cases j
      exact NI17N0
    · dsimp ; intro j
      fin_cases j
      exact NI19N0
      exact NI19N1
      exact NI19N1
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
      exact NI31N1
  β := ![I2N0, I2N1, I3N0, I3N1, I5N0, I5N1, I7N0, I7N1, I11N0, I11N1, I19N0, I19N1, I23N1, I31N1]
  Il := ![[I2N0, I2N1], [I3N0, I3N1, I3N1], [I5N0, I5N1], [I7N0, I7N1], [I11N0, I11N1], [], [], [I19N0, I19N1, I19N1], [I23N1], [], [I31N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
