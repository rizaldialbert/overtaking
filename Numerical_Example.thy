theory Numerical_Example
imports
  Environment_Executable
  Test_Code_Generation_Real_Approx
  Overtaking_rules
begin

text \<open>The lane consists of two lanelets with the same direction. All lane boundaries are
  simply straight lanes.\<close>

definition bound0 :: "(real2 \<times> real2) list" where "bound0 = [((-35,-2.25),(200,-2.251))]"
definition bound1 :: "(real2 \<times> real2) list" where "bound1 = [((-35, 2.25),(200, 2.251))]"
definition bound2 :: "(real2 \<times> real2) list" where "bound2 = [((-35, 6.75),(200, 6.751))]"

text \<open>Interpreting the definition @{term "lane2'"} locale\<close>

global_interpretation l2': lane2' bound0 bound1 bound2
  defines lane_detection = l2'.Lane.lane_detection and
  in_lane = l2'.in_lane2  and
  in_lane' = l2'.Lane.in_lane and
  lines_inside0 = l2'.lane0.lines_inside and
  lines_inside1 = l2'.lane1.lines_inside and
  intersect_boundaries0 = l2'.lane0.intersect_boundaries and
  intersect_boundaries1 = l2'.lane1.intersect_boundaries and
  intersect_right_boundary0 = l2'.lane0.intersect_right_boundary and
  intersect_right_boundary1 = l2'.lane1.intersect_right_boundary and
  intersect_left_boundary0 = l2'.lane0.intersect_left_boundary and
  intersect_left_boundary1 = l2'.lane1.intersect_left_boundary and
  rectangle_inside0 = l2'.lane0.rectangle_inside and
  rectangle_inside1 = l2'.lane1.rectangle_inside and
  lane_boundaries_touched = l2'.Lane.lane_boundaries_touched and
  point_in_drivable_area0 = l2'.lane0.point_in_drivable_area and
  point_in_drivable_area1 = l2'.lane1.point_in_drivable_area and
  direction_right0 = l2'.lane0.direction_right and
  direction_right1 = l2'.lane1.direction_right and
  rectangle_intersect0 = l2'.bound0.rectangle_intersect and
  rectangle_intersect1 = l2'.bound1.rectangle_intersect and
  rectangle_intersect2 = l2'.bound2.rectangle_intersect and
  vertices_inside0 = l2'.lane0.vertices_inside and
  lane_boundaries_touched2 = l2'.lane_boundaries_touched2 and
  vertices_inside1 = l2'.lane1.vertices_inside and
  initial_lane = l2'.Lane.initial_lane and
  start_inc_lane = l2'.Lane.start_inc_lane and
  finish_inc_lane = l2'.Lane.finish_inc_lane and
  increase_lane = l2'.Lane.increase_lane and
  decrease_lane = l2'.Lane.decrease_lane and
  start_dec_lane = l2'.Lane.start_dec_lane and
  finish_dec_lane = l2'.Lane.finish_dec_lane and
  overtaking = l2'.Lane.overtaking and
  overtaking_trace = l2'.Lane.overtaking_trace and
  fast_lane_trace = l2'.Lane.fast_lane_trace and
  merging_trace = l2'.Lane.merging_trace and
  original_lane_trace = l2'.Lane.original_lane_trace and
  time_points_to_ov_bools = l2'.Lane.time_points_to_ov_bools and
  time_points_to_fl_bools = l2'.Lane.time_points_to_fl_bools and
  time_points_to_merge_bools = l2'.Lane.time_points_to_merge_bools and
  time_points_to_ori_bools = l2'.Lane.time_points_to_ori_bools and
  overtaking_checker = l2'.Lane.overtaking_checker and
  onfastlane_checker = l2'.Lane.onfastlane_checker and
  merging_checker = l2'.Lane.merging_checker and
  original_lane_checker = l2'.Lane.original_lane_checker and
  sd_rear_checker = l2'.Lane.sd_rear_checker and
  sd_rear_checker' = l2'.Lane.sd_rear_checker' and
  sd_rears = l2'.Lane.sd_rears and
  sd_rear = l2'.Lane.sd_rear and
  sd_rear' = l2'.Lane.sd_rear' and
  sd_raw_state = l2'.Lane.sd_raw_state and
  vehicles_behind = l2'.Lane.vehicles_behind and
  trim_vehicles_same_lane = l2'.Lane.trim_vehicles_same_lane and
  safe_to_return_trace = l2'.Lane.safe_to_return_trace and
  safe_to_return_checker = l2'.Lane.safe_to_return_checker and
  closest_vehicles_infront_idx = l2'.Lane.closest_vehicles_infront_idx and
  vehicles_infront = l2'.Lane.vehicles_infront and
  sd_raw_state_list' = l2'.Lane.sd_raw_state_list' and
  sd_raw_state_list = l2'.Lane.sd_raw_state_list
  by (unfold_locales) (eval+)

lemma [code]: "start_dec_lane uu i num =
  (case i of
    0 \<Rightarrow> None
  | Suc v \<Rightarrow>
    case uu of
     [] \<Rightarrow> None
  | (rect # rects) \<Rightarrow>
    (case lane_detection rect of Outside \<Rightarrow> None
     | Lane n \<Rightarrow>
         if n = Suc v then start_dec_lane rects n (num + 1) else None
     | Boundaries ns \<Rightarrow>
         if tl ns = [] \<and> hd ns = Suc v then Some (num, rects)
         else None))"
  by (auto split: nat.splits list.splits)

lemma [code]: "finish_dec_lane uu i num =
  (case i of
    0 \<Rightarrow> None
  | Suc v \<Rightarrow>
    case uu of
      [] \<Rightarrow> None
   | (rect # rects) \<Rightarrow>
  (case lane_detection rect of Outside \<Rightarrow> None
   | Lane n \<Rightarrow> if n = Suc v - 1 then Some (num, rects) else None
   | Boundaries ns \<Rightarrow>
       if tl ns = [] \<and> hd ns = Suc v
       then finish_dec_lane rects (Suc v) (num + 1) else None))"
  by (auto split: nat.splits list.splits)

text \<open>Preparing the trace\<close>

definition xpos :: "real list" where
"xpos =
[
         0,    1.6657,    3.3299,    4.9924,    6.6525,    8.3097,    9.9629,   11.6121,   13.2576,   14.8995,   16.5373,   18.1708,   19.7999,   21.4245,   23.0449,   24.6612,
   26.2739,   27.8833,   29.4899,   31.0942,   32.6956,   34.2943,   35.8899,   37.4826,   39.0721,   40.6585,   42.2417,   43.8217,   45.3985,   46.9722,   48.5428,   50.1104,
   51.6749,   53.2366,   54.7955,   56.3516,   57.9051,   59.4560,   61.0044,   62.5505,   64.0943,   65.6359,   67.1755,   68.7131,   70.2490,   71.7831,   73.3156,   74.8467,
   76.3764,   77.9050,   79.4326,   80.9593,   82.4852,   84.0106,   85.5356,   87.0603,   88.5850,   90.1098,   91.6349,   93.1606,   94.6869,   96.2141,   97.7425,   99.2722,
  100.8035,  102.3365,  103.8716,  105.4097,  106.9516,  108.4977,  110.0486,  111.6043,  113.1649,  114.7304,  116.3007,  117.8756,  119.4551,  121.0392,  122.6280,  124.2215,
  125.8199,  127.4233,  129.0319,  130.6458,  132.2650,  133.8893,  135.5186,  137.1525,  138.7910,  140.4335,  142.0797,  143.7293,  145.3821,  147.0375,  148.6949,  150.3541,
  152.0148,  153.6768,  155.3399,  157.0040,  158.6687
]"

definition ypos :: "real list" where
"ypos =
[
   -0.0005,    0.0185,    0.0712,    0.1619,    0.2923,    0.4609,    0.6655,    0.9007,    1.1607,    1.4384,    1.7260,    2.0161,    2.3057,    2.5874,    2.8549,    3.1037,
    3.3271,    3.5250,    3.6917,    3.8293,    3.9450,    4.0410,    4.1199,    4.1843,    4.2365,    4.2785,    4.3123,    4.3393,    4.3608,    4.3780,    4.3916,    4.4023,
    4.4109,    4.4177,    4.4230,    4.4272,    4.4306,    4.4332,    4.4353,    4.4369,    4.4382,    4.4392,    4.4400,    4.4406,    4.4411,    4.4415,    4.4418,    4.4420,
    4.4422,    4.4424,    4.4425,    4.4425,    4.4426,    4.4426,    4.4427,    4.4427,    4.4427,    4.4427,    4.4427,    4.4427,    4.4427,    4.4427,    4.4427,    4.4427,
    4.4427,    4.4426,    4.4256,    4.3786,    4.2998,    4.1888,    4.0469,    3.8764,    3.6807,    3.4639,    3.2304,    2.9854,    2.7336,    2.4800,    2.2291,    1.9851,
    1.7516,    1.5314,    1.3270,    1.1397,    0.9706,    0.8200,    0.6875,    0.5725,    0.4738,    0.3901,    0.3198,    0.2614,    0.2132,    0.1738,    0.1416,    0.1154,
    0.0942,    0.0769,    0.0629,    0.0513,    0.0419
]"

definition oris :: "real list" where
"oris =
[
         0,    0.0102,    0.0244,    0.0425,    0.0625,    0.0830,    0.1036,    0.1220,    0.1383,    0.1511,    0.1603,    0.1656,    0.1689,    0.1678,    0.1633,    0.1557,
    0.1442,    0.1313,    0.1154,    0.1010,    0.0872,    0.0743,    0.0627,    0.0525,    0.0436,    0.0360,    0.0295,    0.0241,    0.0196,    0.0159,    0.0129,    0.0104,
    0.0083,    0.0067,    0.0053,    0.0043,    0.0034,    0.0027,    0.0022,    0.0017,    0.0014,    0.0011,    0.0009,    0.0007,    0.0005,    0.0004,    0.0003,    0.0003,
    0.0002,    0.0002,    0.0001,    0.0001,    0.0001,    0.0001,    0.0001,    0.0000,    0.0000,    0.0000,    0.0000,    0.0000,    0.0000,    0.0000,    0.0000,    0.0000,
    0.0000,    0.0000,   -0.0099,   -0.0235,   -0.0397,   -0.0572,   -0.0749,   -0.0920,   -0.1078,   -0.1217,   -0.1332,   -0.1421,   -0.1483,   -0.1516,   -0.1522,   -0.1502,
   -0.1459,   -0.1397,   -0.1318,   -0.1226,   -0.1125,   -0.1020,   -0.0913,   -0.0807,   -0.0706,   -0.0611,   -0.0523,   -0.0444,   -0.0373,   -0.0312,   -0.0259,   -0.0214,
   -0.0176,   -0.0145,   -0.0119,   -0.0098,   -0.0081
]"

definition lengths :: "real list" where
  "lengths = replicate 101 4.8"

definition widths :: "real list" where
  "widths = replicate 101 2"

definition veloxs :: "real list" where
"veloxs =
[
   16.6667,   16.6596,   16.6519,   16.6401,   16.6242,   16.6017,   16.5709,   16.5368,   16.5027,   16.4650,   16.4239,   16.3803,   16.3360,   16.2915,   16.2484,   16.2078,
   16.1709,   16.1375,   16.1085,   16.0809,   16.0528,   16.0239,   15.9940,   15.9632,   15.9316,   15.8995,   15.8671,   15.8347,   15.8024,   15.7704,   15.7388,   15.7078,
   15.6774,   15.6477,   15.6187,   15.5906,   15.5632,   15.5367,   15.5112,   15.4866,   15.4629,   15.4403,   15.4188,   15.3983,   15.3790,   15.3608,   15.3439,   15.3282,
   15.3138,   15.3008,   15.2891,   15.2789,   15.2702,   15.2630,   15.2575,   15.2535,   15.2513,   15.2509,   15.2523,   15.2555,   15.2607,   15.2679,   15.2772,   15.2885,
   15.3021,   15.3179,   15.3382,   15.3655,   15.3995,   15.4391,   15.4825,   15.5282,   15.5746,   15.6209,   15.6664,   15.7111,   15.7553,   15.7998,   15.8450,   15.8911,
   15.9386,   15.9879,   16.0389,   16.0911,   16.1433,   16.1951,   16.2455,   16.2940,   16.3402,   16.3829,   16.4226,   16.4594,   16.4932,   16.5215,   16.5460,   16.5672,
   16.5856,   16.6016,   16.6152,   16.6264,   16.6352
]"

definition veloys :: "real list" where
"veloys =
[
         0,    0.1692,    0.4065,    0.7073,    1.0404,    1.3816,    1.7223,    2.0276,    2.2965,    2.5071,    2.6553,    2.7370,    2.7850,    2.7597,    2.6766,    2.5442,
    2.3487,    2.1312,    1.8666,    1.6294,    1.4026,    1.1932,    1.0049,    0.8390,    0.6954,    0.5726,    0.4690,    0.3822,    0.3103,    0.2509,    0.2023,    0.1627,
    0.1305,    0.1045,    0.0835,    0.0667,    0.0531,    0.0423,    0.0337,    0.0268,    0.0213,    0.0169,    0.0134,    0.0106,    0.0084,    0.0067,    0.0053,    0.0042,
    0.0033,    0.0026,    0.0021,    0.0017,    0.0013,    0.0010,    0.0008,    0.0007,    0.0005,    0.0004,    0.0003,    0.0003,    0.0002,    0.0002,    0.0001,    0.0001,
    0.0001,    0.0001,   -0.1513,   -0.3615,   -0.6114,   -0.8834,   -1.1619,   -1.4332,   -1.6858,   -1.9103,   -2.0994,   -2.2480,   -2.3530,   -2.4134,   -2.4300,   -2.4051,
   -2.3427,   -2.2476,   -2.1255,   -1.9823,   -1.8242,   -1.6573,   -1.4870,   -1.3183,   -1.1554,   -1.0018,   -0.8597,   -0.7309,   -0.6162,   -0.5156,   -0.4288,   -0.3549,
   -0.2927,   -0.2409,   -0.1981,   -0.1630,   -0.1343
]"

definition velos :: "real2 list" where
  "velos = zip veloxs veloys"

definition max_decelxs :: "real list" where
"max_decelxs =
[
   -8.0000,   -7.9996,   -7.9976,   -7.9928,   -7.9844,   -7.9724,   -7.9571,   -7.9405,   -7.9236,   -7.9088,   -7.8975,   -7.8906,   -7.8862,   -7.8876,   -7.8936,   -7.9032,
   -7.9169,   -7.9311,   -7.9468,   -7.9592,   -7.9696,   -7.9779,   -7.9843,   -7.9890,   -7.9924,   -7.9948,   -7.9965,   -7.9977,   -7.9985,   -7.9990,   -7.9993,   -7.9996,
   -7.9997,   -7.9998,   -7.9999,   -7.9999,   -8.0000,   -8.0000,   -8.0000,   -8.0000,   -8.0000,   -8.0000,   -8.0000,   -8.0000,   -8.0000,   -8.0000,   -8.0000,   -8.0000,
   -8.0000,   -8.0000,   -8.0000,   -8.0000,   -8.0000,   -8.0000,   -8.0000,   -8.0000,   -8.0000,   -8.0000,   -8.0000,   -8.0000,   -8.0000,   -8.0000,   -8.0000,   -8.0000,
   -8.0000,   -8.0000,   -7.9996,   -7.9978,   -7.9937,   -7.9869,   -7.9776,   -7.9661,   -7.9535,   -7.9408,   -7.9291,   -7.9193,   -7.9122,   -7.9083,   -7.9076,   -7.9099,
   -7.9150,   -7.9221,   -7.9307,   -7.9400,   -7.9494,   -7.9584,   -7.9667,   -7.9739,   -7.9801,   -7.9851,   -7.9891,   -7.9921,   -7.9944,   -7.9961,   -7.9973,   -7.9982,
   -7.9988,   -7.9992,   -7.9994,   -7.9996,   -7.9997
]"

definition max_decelys :: "real list" where
"max_decelys =
[
         0,   -0.0812,   -0.1952,   -0.3397,   -0.4997,   -0.6635,   -0.8270,   -0.9736,   -1.1026,   -1.2043,   -1.2768,   -1.3184,   -1.3445,   -1.3361,   -1.3003,   -1.2406,
   -1.1499,   -1.0474,   -0.9209,   -0.8065,   -0.6963,   -0.5941,   -0.5016,   -0.4199,   -0.3488,   -0.2879,   -0.2363,   -0.1931,   -0.1570,   -0.1273,   -0.1028,   -0.0829,
   -0.0666,   -0.0534,   -0.0428,   -0.0342,   -0.0273,   -0.0218,   -0.0174,   -0.0138,   -0.0110,   -0.0087,   -0.0070,   -0.0055,   -0.0044,   -0.0035,   -0.0028,   -0.0022,
   -0.0017,   -0.0014,   -0.0011,   -0.0009,   -0.0007,   -0.0005,   -0.0004,   -0.0003,   -0.0003,   -0.0002,   -0.0002,   -0.0001,   -0.0001,   -0.0001,   -0.0001,   -0.0000,
   -0.0000,   -0.0000,    0.0789,    0.1882,    0.3174,    0.4570,    0.5987,    0.7353,    0.8609,    0.9711,    1.0626,    1.1331,    1.1817,    1.2080,    1.2127,    1.1972,
    1.1634,    1.1137,    1.0510,    0.9782,    0.8983,    0.8144,    0.7292,    0.6451,    0.5643,    0.4883,    0.4182,    0.3549,    0.2987,    0.2496,    0.2073,    0.1713,
    0.1411,    0.1161,    0.0954,    0.0784,    0.0646
]"

definition max_decels :: "real2 list" where
  "max_decels = zip max_decelxs max_decelys"

fun mk_rectangles :: "real list \<Rightarrow> real list \<Rightarrow> real list \<Rightarrow> real list \<Rightarrow> real list \<Rightarrow> rectangle list" where
  "mk_rectangles    []       []      []        []       []    = []" |
  "mk_rectangles (x # xs) (y # ys) (p # ps) (l # ls) (w # ws) = \<lparr>Xcoord = x, Ycoord = y, Orient = p, Length = l, Width = w\<rparr> # mk_rectangles xs ys ps ls ws"

definition rectangles where "rectangles = mk_rectangles xpos ypos oris lengths widths"

definition "test" where "test \<equiv> \<lambda>rect. start_inc_lane rect 0 0"

declare [[ML_print_depth=1000]]

ML\<open>
val rectangles = @{code rectangles};
val test_rectangle = nth rectangles 13;
val test_rectangle2 = nth rectangles 84;
val get_vertices = @{code get_vertices_zero};
val tr_gv = get_vertices test_rectangle2;
val transpose = @{code List.transpose};
val test_rectangle3 = nth rectangles 8;
val get_vertices_rot = @{code get_vertices_rotated_translated};
val rotated3 =  get_vertices_rot test_rectangle3;
val in_lane = @{code in_lane};
val test_in_lane = in_lane test_rectangle
val rectangle_intersect1 = @{code rectangle_intersect1};
val test_intersect1 = rectangle_intersect1 test_rectangle;
val get_lines = @{code get_lines};
val test_get_lines = get_lines test_rectangle;
val first_line = nth test_get_lines 0;
val rectangle_inside1 = @{code rectangle_inside1};
val test_rectin1 = map rectangle_inside1 rectangles;
val vertices_inside1 = @{code vertices_inside1};
val test_inside1 = map vertices_inside1 rectangles;
val lane_detection = @{code lane_detection};
val test_lane_detection = map lane_detection rectangles;
val start_inc_lane = @{code test};
val test_start_inc_lane = start_inc_lane rectangles ;
val increase_lane = @{code increase_lane};
val test_overtaking = increase_lane rectangles;
val decrease_lane = @{code decrease_lane}
val overtaking = @{code overtaking}
val test_overtaking = overtaking rectangles;
val overtaking_trace = @{code overtaking_trace};
val test_overtaking_trace = overtaking_trace rectangles;
val fast_lane_trace = @{code fast_lane_trace}
val test_fast_lane_trace = fast_lane_trace rectangles;
val merging_trace = @{code merging_trace}
val test_merging_trace = merging_trace rectangles;
val original_lane_trace = @{code original_lane_trace};
val test_original_lane_trace = original_lane_trace rectangles;
\<close>

fun mk_raw_state :: "real list \<Rightarrow> real list \<Rightarrow> real list \<Rightarrow> real list \<Rightarrow> real list \<Rightarrow> real2 list \<Rightarrow> real2 list \<Rightarrow> raw_state list" where
  "mk_raw_state    []       []      []        []       []       []       []    = []" |
  "mk_raw_state (x # xs) (y # ys) (p # ps) (l # ls) (w # ws) (v # vs) (a # as) = \<lparr>Xcoord = x, Ycoord = y, Orient = p, Length = l, Width = w, velocity = v, acceleration = a\<rparr> # mk_raw_state xs ys ps ls ws vs as"

definition raw_states where "raw_states = mk_raw_state xpos ypos oris lengths widths velos max_decels"
definition ego_run where "ego_run = (Motorised, raw_states)"

text \<open>Trace for vehicle being overtaken. The length of the trace is equivalent to that of
ego vehicle.\<close>

lemma "length veloxs = 101" unfolding veloxs_def by auto

text \<open>The other vehicle is positioned at @{term "(19,0)"} initially. The rest is calculated by
simply using @{term "s + v * t"}. Each time point is @{term "0.1"} s.\<close>

definition xpos_one :: "real list" where
  "xpos_one = 19 # [19 + 11.1 * 0.1 * t . t \<leftarrow> [1..100]]"

definition ypos_one :: "real list" where
  "ypos_one = replicate 101 0"

definition oris_one :: "real list" where
  "oris_one = replicate 101 0"

definition rectangles_other_one where "rectangles_other_one \<equiv> mk_rectangles xpos_one ypos_one oris_one lengths widths"

text \<open>The vehicle being overtaken is assumed to maintain its current speed. It is not allowed
to accelerate when the vehicle is being overtaken.\<close>

definition veloxs_one :: "real list" where
  "veloxs_one = replicate 101 11.1"

definition veloys_one :: "real list" where
  "veloys_one = replicate 101 0"

definition velos_one :: "real2 list" where
  "velos_one = zip veloxs_one veloys_one"

definition reaction_time :: "real" where
  "reaction_time = 0.5"

definition raw_states_other where "raw_states_other = mk_raw_state xpos_one ypos_one oris_one lengths widths velos_one max_decels"
definition other_one_run where "other_one_run = (Motorised, raw_states_other)"

text \<open>Trace for the second vehicle.\<close>

definition xpos_two :: "real list" where
  "xpos_two = -25 # [-25 + 16.7 * 0.1 * t. t \<leftarrow> [1..100]]"

lemma "length xpos_two = 101" unfolding xpos_two_def by eval

definition ypos_two :: "real list" where
  "ypos_two = replicate 101 4.5"

definition oris_two :: "real list" where
  "oris_two = replicate 101 0"

definition rectangles_other_two where "rectangles_other_two \<equiv> mk_rectangles xpos_two ypos_two oris_two lengths widths"

definition veloxs_two :: "real list" where
  "veloxs_two = replicate 101 16.7"

definition veloys_two :: "real list" where
  "veloys_two = replicate 101 0"

definition velos_two :: "real2 list" where
  "velos_two = zip veloxs_two veloys_two"

definition raw_states_other_two where "raw_states_other_two \<equiv> mk_raw_state xpos_two ypos_two oris_two lengths widths velos_two max_decels"
definition other_two_run where "other_two_run \<equiv> (Motorised, raw_states_other_two)"
definition black_boxes :: black_boxes where "black_boxes = (ego_run, [other_one_run, other_two_run])"

definition toc where "toc \<equiv> overtaking_checker black_boxes"
definition tfl where "tfl \<equiv> onfastlane_checker black_boxes"
definition tm where "tm \<equiv> merging_checker black_boxes"
definition tol where "tol \<equiv> original_lane_checker black_boxes"
definition tsd where "tsd \<equiv> sd_rear_checker black_boxes reaction_time"
definition tsr where "tsr \<equiv> safe_to_return_checker black_boxes reaction_time"

value [code] "toc"
value [code] "tfl"
value [code] "tm"
value [code] "tol"
value [code] "tsd"
value [code] "List.enumerate 0 (zip tol tsd)"

definition eight_list where "eight_list \<equiv> nth_list 73 (map snd (snd black_boxes))"

ML \<open>
val test = @{code sd_rear_checker'} @{code black_boxes} @{code reaction_time};
val other_runs_t = @{code List.transpose} (map snd (snd @{code black_boxes}));
val ego_run = snd (fst @{code black_boxes});
val test = @{code sd_rears} other_runs_t ego_run @{code reaction_time};
val eight_list = @{code eight_list};
val eight_ego = List.nth (ego_run, 73);
val test2 = @{code sd_rear} eight_list eight_ego @{code reaction_time};
val veh_behind = @{code vehicles_behind} eight_list eight_ego;
val sd_rear_prime = @{code sd_rear'} veh_behind eight_ego @{code reaction_time};
(* val sd_raw_state = @{code sd_raw_state} (hd veh_behind) eight_ego @{code reaction_time};
 *)
\<close>

value [code] "tsr"

definition temp where "temp or so \<equiv>  [f or. f \<leftarrow> (map nth_list so)]"
definition temp2 where "temp2 bb so \<equiv> [f (snd (fst bb)) . f \<leftarrow> (map (\<lambda>n xs. xs ! n) so)]"
definition temp3 where "temp3 or ovp \<equiv> [f or. f \<leftarrow> (map (\<lambda>n xss. xss !n) ovp)]"
ML \<open>
val ego_rects = @{code bb_to_rects} @{code black_boxes};
val ov_nums = @{code overtaking} ego_rects;
val start_ovs = map fst ov_nums;
val other_runs = map snd (snd @{code black_boxes});
val choppeds = @{code temp} other_runs start_ovs;
val ego_chopped = @{code temp2} @{code black_boxes} start_ovs;
val overtaken_vehs = map ((fn f => fn p => f (fst p) (snd p)) @{code closest_vehicles_infront_idx})
                                                              (@{code zip} (@{code List.transpose} choppeds) ego_chopped);
val overtaken_vehs' = @{code take_some} overtaken_vehs;
val relevant_trace = @{code temp3} other_runs overtaken_vehs';
val result = @{code sd_raw_state_list} relevant_trace (snd (fst @{code black_boxes})) @{code reaction_time}
val result2 = @{code List.enumerate} @{code "0 :: nat"} (@{code nth} result @{code "0 :: nat"});
List.nth(snd (fst @{code black_boxes}), 36);
List.nth(List.nth (relevant_trace, 0), 36);
\<close>

fun combine_to_trace :: "tr_atom set list list \<Rightarrow> tr_atom set list \<Rightarrow> tr_atom set list" where
  "combine_to_trace [] res = res" |
  "combine_to_trace (x # xs) res = combine_to_trace xs (map (\<lambda>x. union (fst x) (snd x)) (zip x res))"

definition empty_trace :: "tr_atom set list" where "empty_trace \<equiv> replicate 101 {}"
definition complete_trace where "complete_trace \<equiv> combine_to_trace [toc, tfl, tm, tol, tsd, tsr] empty_trace"

definition semantics_ltlf_tr :: "tr_atom set list \<Rightarrow> tr_atom ltlf \<Rightarrow> bool" where
  "semantics_ltlf_tr \<equiv> semantics_ltlf"

ML \<open>
val monitor = @{code monitor_tr};
val monitor2 = @{code semantics_ltlf_tr};
val comp_trace = @{code complete_trace};
val phi1 = @{code \<Phi>1}
val test_phi1 = monitor comp_trace phi1;
val test_phi1' = monitor2 comp_trace phi1;
val phi3_weaker = @{code \<Phi>3_weaker};
val test_phi3_weaker = monitor comp_trace phi3_weaker;
val test_phi3'_weaker = monitor2 comp_trace phi3_weaker;
val phi3 = @{code \<Phi>3};
val test_phi3 = monitor comp_trace phi3;
val phi4 = @{code \<Phi>4};
val test_phi4 = monitor2 comp_trace phi4;
\<close>

end