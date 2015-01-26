package model.utils;

import java.util.Comparator;

import model.data.computation.CandidateResult;

/**
 * @author Ólavur Kjølbro
 */
public /*@ nullable_by_default @*/ class Cmp implements Comparator<CandidateResult> {

	/**
	 * Compares two candidates according to their party id 
	 * and total votes
	 * @param vp1 Total votes of one particular candidate
	 * @param vp2 Total votes of another candidate
	 * @return Returns an integer value (-1, 0, or 1)
	 */
	//@ post cres1.getTotalVotes() < cres2.getTotalVotes() ==> \result == 2;
	//@ post cres1.getTotalVotes() > cres2.getTotalVotes() ==> \result == -2;
	//@ post cres1.getTotalVotes() == cres2.getTotalVotes() && !cres1.isElected() == cres2.isElected() ==> \result == 1;
	//@ post cres1.getTotalVotes() == cres2.getTotalVotes() && cres1.isElected() == !cres2.isElected() ==> \result == -1;
	//@ post cres1.getTotalVotes() == cres2.getTotalVotes() && cres1.isElected() == cres2.isElected() ==> \result == 0;
	@Override
	public final /*@ pure @*/ int compare(
				/*@ non_null @*/ final CandidateResult cres1, 
				/*@ non_null @*/ final CandidateResult cres2) {
		if (cres1.getTotalVotes() < cres2.getTotalVotes()) {
    		return +2;
    	} else if (cres1.getTotalVotes() > cres2.getTotalVotes()) {
    		return -2;
    	} else {
    		if (!cres1.isElected() && cres2.isElected()) {
    			return +1;
    		} else if (cres1.isElected() && !cres2.isElected()) {
    			return -1;
    		}
    		return 0;
    	}
    }

}