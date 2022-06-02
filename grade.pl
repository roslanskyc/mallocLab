#!/usr/bin/perl   
#!/usr/local/bin/perl 
use Getopt::Std;

#########################################################################
# grade-malloclab.pl - Malloc Lab autograder
#
# Copyright (c) 2002, R. Bryant and D. O'Hallaron, All rights reserved.
# May not be used, modified, or copied without permission.
#########################################################################

# What is the distribution of points?
$MAXCORR = 40;   # Max correctness points
$MAXPERF = 45;   # Max performance points
$MAXSTYLE = 10;  # Max style points
$TOTAL = 100;
$TRACEDIR = "./traces";

#
# corr_score - returns correctness score as a function of the
#       number of traces that were handled without any errors.
#
sub corr_score {
    my $numcorrect = $_[0]; # number of traces handled without errors 
    my $numtraces = 11;     # number of traces

    # Score is based on fraction of traces that were correct
    return ($numcorrect / $numtraces) * $MAXCORR;
}

#
# perf_score - returns performance score as a function of the
#      performance index. A solution with a performance index
#      above or equal to $threshhold gets full credit.
#
sub perf_score {
    my $perfindex = $_[0];  # performance index
    my $threshhold = 0.95;  # full credit threshhold
    my $score;

    $score = (($perfindex/100.0) + (1-$threshhold)) * $MAXPERF;
    if ($score > $MAXPERF) {
      $score = $MAXPERF;
    }

    return $score;
}


# autoflush output on every print statement
$| = 1; 

# Any tmp files created by this script are readable only by the user
umask(0077); 

##############
# Main routine
##############

# 
# Make sure the input file exists and is readable
#
open(INFILE, "mm.c") 
    or die "$0: ERROR: could not open file mm.c\n";
close(INFILE);

#
# Compile the driver
#
print "Part 1: Compiling the driver\n\n";
system("(make mdriver.opt)") == 0
    or die "$0: ERROR: Unable to compile mdriver.\n";

#
# Run the driver
#
print "\n\nPart 2: Running the driver with the -g autograder option\n\n";
system("(./mdriver.opt -t $TRACEDIR -vg > results.txt)") == 0 
    or die "$0: ERROR: Unable to run driver program.\n";

#
# Extract the number of correct traces and the performance index
# from the driver output
#
$result = `(cat results.txt)`;
$result =~ /correct:(.*)/;
$numcorrect = $1;
$result =~ /perfidx:(.*)/;
$perfindex = $1;

#
# Compute the number of points for each solution
#
$corr_points = corr_score($numcorrect);
$perf_points = perf_score($perfindex);

#
# Print the grade summary
#
$total = $MAXCORR + $MAXPERF;
print "\n\nPart 3: Grade\n\n";
printf "Correctness:      %3.1f / %3.1f (correct traces = $numcorrect)\n", 
    $corr_points, $MAXCORR;
printf "Performance:      %3.1f / %3.1f (performance index = $perfindex)\n", 
    $perf_points, $MAXPERF;
print "\n";
printf "Autograded total: %3.1f / %2.0f\n", $corr_points + $perf_points, $total;
printf "Not included: 10 possible style points and 5 check-in post points";

system("rm -f results.txt");

exit;
