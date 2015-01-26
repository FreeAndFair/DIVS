package model.data;

import java.io.Serializable;
import java.util.List;

import model.data.map.PollingStation;

/**
 * @author Ólavur Kjølbro
 */
public /*@ nullable_by_default @*/ class Ballot implements Serializable {

	private static final long serialVersionUID = 1L;

	private int ballot_id;
	private PollingStation ps;
	private List<BallotJournal> journal;
	private int invalid_votes;

	//@ invariant ballot_id > 0;
	//@ invariant ps != null;
	//@ invariant journal != null;
	//@ invariant invalid_votes >= 0;

	/**
	 * @param ballot_id Id of ballot in database
	 * @param ps Polling station
	 * @param journal List of ballot journals
	 */
	//@ pre ballot_id > 0;
	//@ post invalid_votes == 0;
	public Ballot(int ballot_id, /*@ non_null @*/ PollingStation ps, 
			/*@ non_null @*/ List<BallotJournal> journal) {
		this.ballot_id = ballot_id;
		this.ps = ps;
		this.journal = journal;
		this.invalid_votes = 0;
	}

	/**
	 * @return The ballot id of the ballot (in the database)
	 */
	public /*@ pure @*/ int getBallotId() {
		return ballot_id;
	}

	/**
	 * @return The polling station to which the ballot belongs
	 */
	public /*@ pure @*/ PollingStation getPs() {
		return ps;
	}

	/**
	 * @return The list of ballot journals belonging to this ballot
	 */
	public /*@ pure @*/ List<BallotJournal> getJournal() {
		return journal;
	}

	/**
	 * @return the invalid_votes
	 */
	public /*@ pure @*/ int getInvalidVotes() {
		return invalid_votes;
	}

	/**
	 * @param invalid_votes the invalid_votes to set
	 */
	//@ pre inv_votes >= 0;
	//@ post invalid_votes == inv_votes;
	//@ assignable invalid_votes;
	public void setInvalidVotes(int inv_votes) {
		this.invalid_votes = inv_votes;
	}

	/**
	 * @return  A string informing about the instance
	 */
	@Override
	public /*@ pure @*/ String toString() {
		return "Ballot - ps: "+ps.getName()+";invalid votes: "+invalid_votes+";journal size: "+journal.size();
	}

}