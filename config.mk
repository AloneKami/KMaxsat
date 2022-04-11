BUILD_DIR?=build
MAXPRE?=-D MAXPRE
USESCIP?=-D USE_SCIP -pthread
BIGWEIGHTS?=#-D BIG_WEIGHTS
MINISATP_RELSYM?=
MINISATP_REL?=-std=c++11 -O3 -D NDEBUG -Wno-strict-aliasing -D COMINISATPS   -D MAXPRE -D USE_SCIP -pthread  -D MAXPRE -D USE_SCIP -pthread  -D MAXPRE -D USE_SCIP -pthread  $(MAXPRE) $(USESCIP) $(BIGWEIGHTS)
MINISATP_DEB?=-std=c++11 -O0 -D DEBUG  -Wno-strict-aliasing -D COMINISATPS   -D MAXPRE -D USE_SCIP -pthread  -D MAXPRE -D USE_SCIP -pthread  -D MAXPRE -D USE_SCIP -pthread  $(MAXPRE) $(USESCIP) $(BIGWEIGHTS)
MINISATP_PRF?=-std=c++11 -O3 -D NDEBUG -Wno-strict-aliasing -D COMINISATPS   -D MAXPRE -D USE_SCIP -pthread  -D MAXPRE -D USE_SCIP -pthread  -D MAXPRE -D USE_SCIP -pthread  $(MAXPRE) $(USESCIP) $(BIGWEIGHTS)
MINISATP_FPIC?=-fpic
MINISAT_INCLUDE?=-I/include -I/include/minisat -I../cominisatps
MINISAT_LIB?=-L/lib -L../cominisatps/simp -l_release -D USE_SCIP -pthread -D USE_SCIP -pthread -D USE_SCIP -pthread $(USESCIP)
ifneq ($(MAXPRE),)
MCL_INCLUDE?=-I../maxpre/src -I../scipoptsuite-7.0.3/scip/src -I../scipoptsuite-7.0.3/build/scip -I../scipoptsuite-7.0.3/scip/src -I../scipoptsuite-7.0.3/build/scip -I../scipoptsuite-7.0.3/scip/src -I../scipoptsuite-7.0.3/build/scip
MCL_LIB?=-L../maxpre/src/lib -lmaxpre -L../scipoptsuite-7.0.3/build/lib -lscip -lsoplex-pic -L../scipoptsuite-7.0.3/build/lib -lscip -lsoplex-pic -L../scipoptsuite-7.0.3/build/lib -lscip -lsoplex-pic
else
MCL_INCLUDE?=
MCL_LIB?=
endif
ifneq ($(USESCIP),)
MCL_INCLUDE+=-I../scipoptsuite-7.0.3/scip/src -I../scipoptsuite-7.0.3/build/scip
MCL_LIB+=-L../scipoptsuite-7.0.3/build/lib -lscip -lsoplex-pic
endif
prefix?=
