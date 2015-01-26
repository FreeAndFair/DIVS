package national.gateways.database;

import java.sql.Connection;
import java.sql.PreparedStatement;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.util.ArrayList;
import java.util.List;

import national.ElectionConstants;
import national.ElectionStatus;
import national.data.Ballot;
import national.data.BallotJournal;
import national.data.Candidate;
import national.data.Party;
import national.data.computation.ConstituencyResult;
import national.data.computation.PartyResult;
import national.data.computation.ProvinceResult;
import national.data.computation.CandidateResult;
import national.data.map.Constituency;
import national.data.map.District;
import national.data.map.PollingStation;
import national.data.map.Province;
import national.utils.DivsException;
import national.utils.LocalDB;

/**
 * @author Ólavur Kjølbro
 */
public /*@ nullable_by_default @*/ class DatabaseGateway implements DB_interface {
	
	private static DatabaseGateway instance;

	protected static Connection local;
	
	//@ invariant local != null;

	/**
	 * Singleton method that returns the DatabaseGateway instance
	 * @param jdbc_driver The jdbc driver of the database
	 * @param db_url The URL of the database
	 * @return Returns the DatabaseGateway instance
	 * @throws DivsException When something is wrong with e.g. connect to db
	 */
	//@ post (((\old(instance) == null || \old(local) == null) ==> instance != null) || local != null) || local != null;
	//@ assignable instance, local;
	//@ signals (DivsException d) (d instanceof DivsException);
    public static DatabaseGateway getInstance(
    		/*@ non_null @*/ String jdbc_driver, 
    		/*@ non_null @*/ String db_url) throws DivsException {
    	if (instance == null || local == null) {
           	instance = new DatabaseGateway(jdbc_driver, db_url);
    	}
    	return instance;
    }

    //@ post local != null;
    //@ assignable local;
	//@ signals (DivsException d) (d instanceof DivsException);
	private DatabaseGateway(
			/*@ non_null @*/ String jdbc_driver, 
			/*@ non_null @*/ String db_url) throws DivsException {
		local = LocalDB.getConnection(jdbc_driver, db_url);
		if (local == null) {
			throw new DivsException(DivsException.ERROR_SQL,
				"Cannot connect to local database");}
	}

	/**
	 * Method calculates the total number of valid votes casted in 
	 * the election - possibly in a certain province
	 * @param temp_final Either preliminary or final result
	 * @param pid Province id in the database. If 0 then all are in
	 * @return Returns the total number of valid votes
	 * @throws DivsException Throws exception when e.g. something is 
	 * 		wrong with db connection
	 */
	@Override
	public /*@ pure @*/ int countTotalValidVotes(int temp_final, int pid) throws DivsException {
		String select = "select sum(party_votes+personal_votes) from Votes v, BallotJournal bj, Party p" +
						(pid>0?", Ballot b, District d, Constituency c ":"") +
						" where bj.bj_id = v.bj_id and bj.party_id = p.party_id" +
						(pid>0?" and b.ballot_id = bj.ballot_id and d.district_id = b.district_id and d.constituency_id = c.constituency_id ":"") +
						" and v.temp_final = ?" +
						(pid>0?" and c.province_id = ?":"");
		try {
			PreparedStatement pstmt = local.prepareStatement(select);
			pstmt.setInt(1, temp_final);
			if (pid > 0) {
				pstmt.setInt(2, pid);
			}
			ResultSet res = pstmt.executeQuery();
			res.next();
			return res.getInt(1);
		} catch (SQLException e) {
			throw new DivsException(DivsException.ERROR_SQL,
					"Count total valid votes:\n"+e.getMessage());
		}
	}

	/**
	 * Method calculates the total number of INvalid votes casted in
	 * the election
	 * @param temp_final Either preliminary or final result
	 * @param pid Province id in the database
	 * @return Returns the total number of INvalid votes
	 * @throws DivsException Throws exception when e.g. something is 
	 * 		wrong with db connection
	 */
	@Override
	public /*@ pure @*/ int countTotalInvalidVotes(
							int temp_final, int pid) throws DivsException {
		String select = "select sum(votes) from InvalidVotes v, Ballot b" +
						(pid>0?", District d, Constituency c":"") +
						" where b.ballot_id = v.ballot_id " +
						(pid>0?" and d.district_id = b.district_id and d.constituency_id = c.constituency_id":"") +
						" and v.temp_final = ?" +
						(pid>0?" and c.province_id = ?":"");
		try {
			//System.out.println(select);
			int retval = 0;
			PreparedStatement pstmt = local.prepareStatement(select);
			pstmt.setInt(1, temp_final);
			if (pid > 0) {
				pstmt.setInt(2, pid);
			}
			ResultSet res = pstmt.executeQuery();
			res.next();
			retval = res.getInt(1);
			return retval;
		} catch (SQLException e) {
			throw new DivsException(DivsException.ERROR_SQL,
				"Count total invalid votes:\n"+e.getMessage());
		}
	}

	/**
	 * Method returns a polling station with a certain ps_id
	 * @param ps_id Id of polling station in the database
	 * @return Polling station
	 * @throws DivsException Throws exception when e.g. something is 
	 * 		wrong with db connection
	 */
	//@ pre ps_id >= 0;
	@Override
	public /*@ pure @*/ PollingStation getPollingStation(int ps_id) throws DivsException {
		String select = "select name, district_id, no_of_reg_voters, open_state " +
						"from PollingStation where ps_id = ?";
		try {
			PreparedStatement pstmt = local.prepareStatement(select);
			pstmt.setInt(1, ps_id);
			ResultSet res = pstmt.executeQuery();
			res.next();
			String name = res.getString(1).trim();
			int district_id = res.getInt(2), 
				no_of_reg_voters = res.getInt(3), 
				open_state = res.getInt(4);
			District d = this.getDistrict(district_id);
			PollingStation p = new PollingStation(ps_id, 
					d, name, no_of_reg_voters);
			if (open_state == ElectionStatus.PS_NOT_OPEN || open_state == ElectionStatus.PS_OPEN || open_state == ElectionStatus.PS_CLOSED) {
				if (p.getOpenStatus() != open_state) {p.open();}
				if (p.getOpenStatus() != open_state) {p.close();}
			}
			pstmt.close();
			return p;
		} catch (SQLException e) {
			throw new DivsException(DivsException.ERROR_SQL,
					"Fetch polling station: ("+ ps_id +")\n"+e.getMessage());
		}
	}

	/**
	 * Method returns the ballot belonging to a certain polling
	 * station. Ballot contains a socalled journal with everything 
	 * that the voter can cast his/her vote on
	 * @param ps Polling station to which the ballot belongs
	 * @return Ballot belonging to a certain district
	 * @throws DivsException Throws exception when e.g. something is 
	 * 		wrong with db connection
	 */
	@Override
	public /*@ pure @*/ Ballot getBallot(/*@ non_null @*/ PollingStation ps) throws DivsException {
		String select = "select b.ballot_id " +
					"from PollingStation p, Ballot b " +
					"where p.district_id = b.district_id" +
					" and p.ps_id = ? order by p.district_id, p.ps_id";
		try {
			PreparedStatement pstmt = local.prepareStatement(select);
			pstmt.setInt(1, ps.getPsId());
			ResultSet res = pstmt.executeQuery();
			res.next();
			int ballot_id;
			try {
				ballot_id = res.getInt(1);
			} catch (SQLException e) {
				return null;
			}
			res.close();
	
			select = "select p.party_id, p.name, p.standing, case when p.letter is not null then p.letter else (select p2.letter from Party p2 where p2.party_id = c.party_id) end as letter, c.candidate_id, c.name, c.cpr, c.position, c.address, bj.bj_id " +
						"from BallotJournal bj left outer join Party p on p.party_id = bj.party_id left outer join Candidate c on c.candidate_id = bj.candidate_id " +
						"where ballot_id = ? " +
						"order by letter, bj.standing, c.name";
			pstmt = local.prepareStatement(select);
			pstmt.setInt(1, ballot_id);
			res = pstmt.executeQuery();
			
			ArrayList<BallotJournal> journal = new ArrayList<BallotJournal>();
			int party_id; //, old_party_id = -1;
			Party p = null; // references is ok?
			while (res.next()) {
				party_id = res.getInt(1);
				if (party_id > 0) {
					p = new Party(party_id, res.getString(2), 
							res.getString(4), res.getInt(3), false);
					BallotJournal bjp = new BallotJournal(p, res.getInt(10));
					journal.add(bjp);
				} else {
					Candidate c = new Candidate(res.getInt(5), res.getString(6).trim(), 
							res.getString(7).trim(), p, res.getString(8).trim(), 
							res.getString(9).trim());
					BallotJournal bjc = new BallotJournal(c, res.getInt(10));
					journal.add(bjc);					
				}
			}
			Ballot retval = new Ballot(ballot_id, ps, journal);
			return retval;
		} catch (SQLException e) {
			e.printStackTrace();
			throw new DivsException(DivsException.ERROR_SQL,
					"Fetch ballot:\n"+e.getMessage());
		}
	}

	/**
	 * Method checks if results are registered for a certain
	 * polling station
	 * @param ps Pollin station
	 * @param temp_final Preliminary or final
	 * @return Returns true if results are registered
	 * @throws DivsException Throws exception when e.g. something is 
	 * 		wrong with db connection
	 */
	public /*@ pure @*/ boolean isResultRegistered(
			/*@ non_null @*/ PollingStation ps, int temp_final) throws DivsException {
		String select = "select count(*) from Votes where ps_id = ? and temp_final = ?";
		try {
			PreparedStatement pstmt = local.prepareStatement(select);
			pstmt.setInt(1, ps.getPsId());
			pstmt.setInt(2, temp_final);
			ResultSet res = pstmt.executeQuery();
			res.next();
			if (res.getInt(1) == 0) {
				return false;
			} else {
				return true;
			}
		} catch (SQLException e) {
			throw new DivsException(DivsException.ERROR_SQL,
				"Fetch provinces:\n"+e.getMessage());
		}
	}

	/**
	 * Method clears all preliminary or final, valid and invalid 
	 * votes of a certain polling station from the database 
	 * @param ps Polling station
	 * @param temp_final Preliminary or final
	 * @throws DivsException Throws exception when e.g. something is 
	 * 		wrong with db connection
	 */
	public void clearResult(
			/*@ non_null @*/ PollingStation ps, int temp_final) throws DivsException {
		String delete1 = "delete from Votes where ps_id = ? and temp_final = ?";
		try {
			PreparedStatement pstmt = local.prepareStatement(delete1);
			pstmt.setInt(1, ps.getPsId());
			pstmt.setInt(2, temp_final);
			pstmt.executeUpdate();
		} catch (SQLException e) {
			throw new DivsException(DivsException.ERROR_SQL,
					"Clear result of polling station ("+ps.getPsId()+"):\n"
					+e.getMessage());
		}
	}

	/**
	 * Method registeres the preliminary or final result of a polling 
	 * station in the database
	 * @param ballot Ballot belonging to a polling station
	 * @param temp_final Either preliminary or final result
	 * @throws DivsException Throws exception when e.g. something is 
	 * 		wrong with db connection
	 */
	@Override
	public void registerResult(/*@ non_null @*/ Ballot ballot,
									int temp_final) throws DivsException {
		String insert = "insert into Votes " +
						"(ps_id, temp_final, bj_id, party_votes, personal_votes) " +
						"values (?, ?, ?, ?, ?)";
		String insert_invv = "insert into InvalidVotes (ballot_id, ps_id, temp_final, votes) " +
						"values (?, ?, ?, ?)";
		try {
			local.setAutoCommit(false);
			
			PreparedStatement pstmt;
			BallotJournal bj;
			if (this.isResultRegistered(ballot.getPs(), temp_final)) {
				this.clearResult(ballot.getPs(), temp_final);
			}
			for (int i = 0; i < ballot.getJournal().size(); i++) {
				bj = ballot.getJournal().get(i);
				pstmt = local.prepareStatement(insert);
				pstmt.setInt(1, ballot.getPs().getPsId());
				pstmt.setInt(2, temp_final);
				pstmt.setInt(3, bj.getBjId());
				pstmt.setInt(4, bj.getPartyVotesInt());
				pstmt.setInt(5, bj.getPersonalVotesInt());
				pstmt.executeUpdate();
			}
			pstmt = local.prepareStatement(insert_invv);
			pstmt.setInt(1, ballot.getBallotId());
			pstmt.setInt(2, ballot.getPs().getPsId());
			pstmt.setInt(3, temp_final);
			pstmt.setInt(4, ballot.getInvalidVotes());
			pstmt.executeUpdate();
			pstmt.close();

			local.commit();
			local.setAutoCommit(true);

		} catch (SQLException e) {
			throw new DivsException(DivsException.ERROR_SQL,
					"Store result from polling station " +
					"(id: "+ballot.getPs().getPsId()+"):\n"+
					e.getMessage());
		}
	}

	/**
	 * Method fetches all counted votes from the database grouped by 
	 * party and constituency. Constituency results also contain 
	 * the independent candidates
	 * @return List of results from constituency  
	 * @throws DivsException Throws exception when e.g. something is 
	 * 		wrong with db connection
	 */
	@Override
	public /*@ pure @*/ List<ConstituencyResult> getConstituencyResult(int temp_final) throws DivsException {
		List<Province> provinces = this.getProvinces();
		List<Constituency> constituencies = this.getConstituencies(provinces);
		List<Party> parties = getParties();
		boolean indep_cand = true;
		List<Candidate> candidates = getCandidates(parties, indep_cand);
		try {
			String select_party_votes = "select bj.party_id, sum(v.party_votes + v.personal_votes) from Votes v, BallotJournal bj, Ballot b, District d where v.bj_id = bj.bj_id and bj.ballot_id = b.ballot_id and b.district_id = d.district_id and v.temp_final = ? and bj.party_id is not null and d.constituency_id = ? group by bj.party_id";
			String select_invalid_votes = "select sum(votes) from InvalidVotes iv, Ballot b, District d where iv.ballot_id = b.ballot_id and b.district_id = d.district_id and iv.temp_final = ? and d.constituency_id = ?";
			PreparedStatement pstmt;
			ResultSet res;
			List<ConstituencyResult> result = new ArrayList<ConstituencyResult>();
			int electable;
			/*
			 * For every constituency...
			 */
			for (int i = 0; i < constituencies.size(); i++) {
				ConstituencyResult cr = new ConstituencyResult(constituencies.get(i));
				List<PartyResult> party_result = new ArrayList<PartyResult>();
				pstmt = local.prepareStatement(select_party_votes);
				pstmt.setInt(1, temp_final);
				pstmt.setInt(2, constituencies.get(i).getConstituencyId());
				res = pstmt.executeQuery();
				while (res.next()) {
					/*
					 * ...we add the votes each party has got to the list
					 */
					PartyResult pres = new PartyResult(
							this.locateParty(res.getInt(1), parties),
							ElectionConstants.DHONDT);
					pres.setTotalVotes(res.getInt(2));
					party_result.add(pres);
				}
				cr.setPartyResult(party_result);
				
				pstmt = local.prepareStatement(select_invalid_votes);
				pstmt.setInt(1, temp_final);
				pstmt.setInt(2, constituencies.get(i).getConstituencyId());
				res = pstmt.executeQuery();
				res.next();
				cr.setInvalidVotes(res.getInt(1));
				
				result.add(cr);
			}

			/*
			 * For all constituencies...
			 */
			String select_ind_cand_votes = "select bj.candidate_id, sum(v.party_votes + v.personal_votes) from Votes v, BallotJournal bj, Candidate ca, Ballot b, District d where v.bj_id = bj.bj_id and ca.candidate_id = bj.candidate_id and bj.ballot_id = b.ballot_id and b.district_id = d.district_id and v.temp_final = ? and bj.party_id is null and ca.party_id is null and d.constituency_id = ? group by bj.candidate_id";
			ConstituencyResult cr;
			for (int i = 0; i < result.size(); i++) {
				cr = result.get(i);
				List<CandidateResult> independent = new ArrayList<CandidateResult>();
				pstmt = local.prepareStatement(select_ind_cand_votes);
				pstmt.setInt(1, temp_final);
				pstmt.setInt(2, constituencies.get(i).getConstituencyId());
				res = pstmt.executeQuery();
				while (res.next()) {
					/*
					 * ...we must add the personal votes for independent candidates too
					 */
					CandidateResult cres = new CandidateResult(
							this.locateCandidate(res.getInt(1), candidates));
					cres.setPersonalVotes(res.getInt(2));
					independent.add(cres);
				}
				cr.setIndependentCandidates(independent);
				
				/*
				 * Last we also need to inform about how many independent 
				 * candidates got more than 0 votes, and therefore can
				 * get elected 
				 */
				electable = 0;
				for (int j = 0; j < independent.size(); j++) {
					if (independent.get(j).getTotalVotes() > 0) {electable++;}
				}
				cr.setElectableIndpendentCandidates(electable);
			}
			
			return result;
		} catch (SQLException e) {
			throw new DivsException(DivsException.ERROR_SQL,
					"Fetch constituency result from database:\n"+e.getMessage());
		}
	}

	/**
	 * Method fetches all counted votes from the database grouped by
	 * party on national level.
	 * @return Returns a list of party result
	 * @throws DivsException Throws exception when e.g. something is 
	 * 		wrong with db connection
	 */
	@Override
	public /*@ pure @*/ List<PartyResult> getNationalResult(int temp_final) throws DivsException {
		List<Party> parties = getParties();
		try {
			String select = "select bj.party_id, sum(v.party_votes + v.personal_votes) from Votes v, BallotJournal bj where v.bj_id = bj.bj_id and v.temp_final = ? and bj.party_id is not null group by bj.party_id";
			PreparedStatement pstmt;
			ResultSet res;
			List<PartyResult> result = new ArrayList<PartyResult>();

			pstmt = local.prepareStatement(select);
			pstmt.setInt(1, temp_final);
			res = pstmt.executeQuery();
			while (res.next()) {
				/*
				 * Instantiate party result, add votes, and the add it to the list
				 */
				PartyResult pres = new PartyResult(
						this.locateParty(res.getInt(1), parties), 
						ElectionConstants.DHONDT);
				pres.setTotalVotes(res.getInt(2));
				result.add(pres);
			}
			return result;
		} catch (SQLException e) {
			throw new DivsException(DivsException.ERROR_SQL,
					"Fetch constituency result from database:\n"+e.getMessage());
		}
	}

	/**
	 * Method fetches all counted votes from the database grouped by
	 * party and province. 
	 * @return Returns a list of province result 
	 * @throws DivsException Throws exception when e.g. something is 
	 * 		wrong with db connection
	 */
	@Override
	public /*@ pure @*/ List<ProvinceResult> getProvinceResult(int temp_final) throws DivsException {
		List<Province> provinces = this.getProvinces();
		List<Party> parties = getParties();
		try {
			String select = "select bj.party_id, sum(v.party_votes + v.personal_votes) from Votes v, BallotJournal bj, Ballot b, District d, Constituency c where v.bj_id = bj.bj_id and bj.ballot_id = b.ballot_id and b.district_id = d.district_id and d.constituency_id = c.constituency_id and v.temp_final = ? and bj.party_id is not null and c.province_id = ? group by bj.party_id";
			PreparedStatement pstmt;
			ResultSet res;
			List<ProvinceResult> result = new ArrayList<ProvinceResult>();

			/*
			 * For every province...
			 */
			for (int i = 0; i < provinces.size(); i++) {
				ProvinceResult pr = new ProvinceResult(provinces.get(i));
				List<PartyResult> party_result = new ArrayList<PartyResult>();
				pstmt = local.prepareStatement(select);
				pstmt.setInt(1, temp_final);
				pstmt.setInt(2, provinces.get(i).getProvinceId());
				res = pstmt.executeQuery();
				while (res.next()) {
					/*
					 * ...we add the votes each party has got to the list
					 */
					PartyResult pres = new PartyResult(
							this.locateParty(res.getInt(1), parties),
							ElectionConstants.SAINTE_LAGUE);
					pres.setTotalVotes(res.getInt(2));
					party_result.add(pres);
				}
				pr.setPartyResult(party_result);
				pr.setValidVotes(this.countTotalValidVotes(temp_final, pr.getProvince().getProvinceId()));
				result.add(pr);
			}
			return result;
		} catch (SQLException e) {
			throw new DivsException(DivsException.ERROR_SQL,
					"Fetch constituency result from database:\n"+e.getMessage());
		}
	}

	/**
	 * Method add to the list of results from constituency the party
	 * result, which consists among other things of the candidates
	 * running for the party. Method must therefore be callled before 
	 * computing step 6. 
	 * @param List of constituency results already existing  
	 * @throws DivsException Throws exception when e.g. something is 
	 * 		wrong with db connection
	 */
	@Override
	public void	addCandidatesToConstituencyResult(List<ConstituencyResult> const_result) throws DivsException {
		List<Party> parties = getParties();
		List<Candidate> candidates = getCandidates(parties, false);
		try {
			PreparedStatement pstmt;
			ResultSet res;
			ConstituencyResult cr;

			/*
			 * For every constituency...
			 */
			String select_cand_votes = "select bj.candidate_id, sum(v.party_votes), sum(v.personal_votes) from Votes v, BallotJournal bj, Candidate ca, Ballot b, District d where v.bj_id = bj.bj_id and ca.candidate_id = bj.candidate_id and bj.ballot_id = b.ballot_id and b.district_id = d.district_id and v.temp_final = ? and bj.party_id is null and d.constituency_id = ? and ca.party_id = ? group by bj.candidate_id";
			for (int i = 0; i < const_result.size(); i++) {
				cr = const_result.get(i);
				List<PartyResult> party_results = new ArrayList<PartyResult>();
				/*
				 * ..and every party...
				 * (assuming that party_result list has the same parties as 
				 * the party_result list)
				 */
				for (int j = 0; j < cr.getPartyResult().size(); j++) {
					PartyResult pres = new PartyResult(
							cr.getPartyResult().get(j).getParty(),
							ElectionConstants.DHONDT);

					List<CandidateResult> pers_votes = new ArrayList<CandidateResult>();
					pstmt = local.prepareStatement(select_cand_votes);
					pstmt.setInt(1, ElectionConstants.FINAL_);
					pstmt.setInt(2, const_result.get(i).getConstituency().getConstituencyId());
					pstmt.setInt(3, pres.getParty().getPartyId());
					res = pstmt.executeQuery();
					while (res.next()) {
						/*
						 * ...fetch the candidates
						 */
						CandidateResult cres = new CandidateResult(
								this.locateCandidate(res.getInt(1), candidates));
						cres.setPartyVotes(res.getInt(2));
						cres.setPersonalVotes(res.getInt(3));
						pres.setTotalVotes(pres.getTotalVotes()+
								cres.getPartyVotes()+cres.getPersonalVotes());
						pers_votes.add(cres);
					}
					pres.setCandidateResults(pers_votes);
					party_results.add(pres);
				}
				const_result.get(i).setPartyResult(party_results);
			}
		} catch (SQLException e) {
			throw new DivsException(DivsException.ERROR_SQL,
					"Fetch constituency result from database:\n"+e.getMessage());
		}
	}

	/**
	 * Method clears all preliminary or final, valid and invalid 
	 * votes from the database 
	 * @param temp_final Preliminary or final
	 * @throws DivsException Throws exception when e.g. something is 
	 * 		wrong with db connection
	 */
	public void clearResults(int temp_final) throws DivsException {
		String delete1 = "delete from Votes where temp_final = ?";
		String delete2 = "delete from InvalidVotes where temp_final = ?";
		try {
			PreparedStatement pstmt = local.prepareStatement(delete1);
			pstmt.setInt(1, temp_final);
			pstmt.execute();
			pstmt = local.prepareStatement(delete2);
			pstmt.setInt(1, temp_final);
			pstmt.execute();
		} catch (SQLException e) {
			throw new DivsException(DivsException.ERROR_SQL,
					"Clear results:\n"+e.getMessage());
		}
	}

	/**
	 * Method opens a certain polling station and saves the state in
	 * the database
	 * @param ps The polling station
	 * @throws DivsException Throws exception when e.g. something is 
	 * 		wrong with db connection
	 */
	@Override
	public void openPollingStation(PollingStation ps) throws DivsException {
		String update = "update PollingStation set open_state = ? where ps_id = ?";
		try {
			PreparedStatement pstmt = local.prepareStatement(update);
			pstmt.setInt(1, ElectionStatus.PS_OPEN);
			pstmt.setInt(2, ps.getPsId());
			pstmt.executeUpdate();
		} catch (SQLException e) {
			throw new DivsException(DivsException.ERROR_SQL,
					"Open polling station:\n"+e.getMessage());
		}
	}

	/**
	 * Method closes a certain polling station and saves the state
	 * in the database
	 * @param ps The polling station
	 * @throws DivsException Throws exception when e.g. something is 
	 * 		wrong with db connection
	 */
	@Override
	public void closePollingStation(PollingStation ps) throws DivsException {
		String update = "update PollingStation set open_state = ? where ps_id = ?";
		try {
			PreparedStatement pstmt = local.prepareStatement(update);
			pstmt.setInt(1, ElectionStatus.PS_CLOSED);
			pstmt.setInt(2, ps.getPsId());
			pstmt.executeUpdate();
		} catch (SQLException e) {
			throw new DivsException(DivsException.ERROR_SQL,
					"Close polling station:\n"+e.getMessage());
		}
	}

	/**
	 * Reset all polling stations to the initial non-open state 
	 * @throws DivsException Throws exception when e.g. something is 
	 * 		wrong with db connection
	 */
	public void resetPollingStations() throws DivsException {
		String update = "update PollingStation set open_state = ?";
		try {
			PreparedStatement pstmt = local.prepareStatement(update);
			pstmt.setInt(1, ElectionStatus.PS_NOT_OPEN);
			pstmt.executeUpdate();
		} catch (SQLException e) {
			throw new DivsException(DivsException.ERROR_SQL,
					"Reset polling stations:\n"+e.getMessage());
		}
	}

	/**
	 * Method reads the open state of a polling station from the 
	 * database
	 * @param ps The polling station
	 * @throws DivsException Throws exception when e.g. something is 
	 * 		wrong with db connection
	 */
	@Override
	public /*@ pure @*/ int getOpenStatus(PollingStation ps) throws DivsException {
		String update = "select open_state from PollingStation where ps_id = ?";
		try {
			PreparedStatement pstmt = local.prepareStatement(update);
			pstmt.setInt(1, ps.getPsId());
			ResultSet res = pstmt.executeQuery();
			res.next();
			return res.getInt(1);
		} catch (SQLException e) {
			throw new DivsException(DivsException.ERROR_SQL,
					"Get open state of polling station:\n"+e.getMessage());
		}
	}
	
	/**
	 * Method checks if all polling stations have closed
	 * @throws DivsException Throws exception when e.g. something is 
	 * 		wrong with db connection
	 */
	@Override
	public /*@ pure @*/ boolean areAllClosed() throws DivsException {
		String select = "select count(*) from PollingStation where ps_id > 0 and open_state <> ?";
		try {
			PreparedStatement pstmt = local.prepareStatement(select);
			pstmt.setInt(1, ElectionStatus.PS_CLOSED);
			ResultSet res = pstmt.executeQuery();
			res.next();
			int count = res.getInt(1);
			return count == 0;
		} catch (SQLException e) {
			throw new DivsException(DivsException.ERROR_SQL,
					"Are all closed:\n"+e.getMessage());
		}
	}

	/**
	 * Method checks if all polling stations have submitted their 
	 * preliminary or final result
	 * @param temp_final Preliminary or final counting 
	 * @return Returns true if all results are submited. False otherwise
	 * @throws DivsException Throws exception when e.g. something is 
	 * 		wrong with db connection
	 */
	@Override
	public /*@ pure @*/ boolean checkCounting(int temp_final) throws DivsException {
		String count_polling_stations = "select count(*) from PollingStation where ps_id > 0";
		String count_counted = "select distinct ps_id from Votes where temp_final = ? and ps_id in (select ps_id from PollingStation where ps_id > 0)";
		try {
			PreparedStatement pstmt = local.prepareStatement(count_polling_stations);
			ResultSet res = pstmt.executeQuery();
			res.next();
			int ps_count = res.getInt(1), counted = 0;
			
			pstmt = local.prepareStatement(count_counted);
			pstmt.setInt(1, temp_final);
			res = pstmt.executeQuery();
			while(res.next()) {
				counted++;
			}
			if (ps_count > counted) {
				return false;
			} else {
				return true;
			}
		} catch (SQLException e) {
			throw new DivsException(DivsException.ERROR_SQL,
					"Check counting:\n"+e.getMessage());
		}
	}

	/**
	 * Method fetches all provinces from the database
	 * @return A list of all provinces
	 * @throws DivsException Throws exception when e.g. something is 
	 * 		wrong with db connection
	 */
	private /*@ pure @*/ List<Province> getProvinces() throws DivsException {
		String select = "select province_id, name, constituency_seats, additional_seats from Province order by province_id";
		try {
			PreparedStatement pstmt = local.prepareStatement(select);
			ResultSet res = pstmt.executeQuery();
			List<Province> retval = new ArrayList<Province>();
			while (res.next()) {
				Province p = new Province(res.getInt(1), res.getString(2).trim(), res.getInt(3), res.getInt(4));
				retval.add(p);
			}
			return retval;
		} catch (SQLException e) {
			throw new DivsException(DivsException.ERROR_SQL,
					"Fetch provinces:\n"+e.getMessage());
		}
	}

	/**
	 * Method fetches all constituencies from the database. Method 
	 * uses the already fetched list of provinces to make references
	 * to provinces consistent
	 * @param provinces A list of all provinces
	 * @return A list of all constituencies
	 * @throws DivsException Throws exception when e.g. something is 
	 * 		wrong with db connection
	 */
	private /*@ pure @*/ List<Constituency> getConstituencies(			/*@ non_null @*/ List<Province> provinces) throws DivsException {
		String select = "select constituency_id, province_id, name, constituency_seats from Constituency order by constituency_id";
		try {
			PreparedStatement pstmt = local.prepareStatement(select);
			ResultSet res = pstmt.executeQuery();
			List<Constituency> constituencies = new ArrayList<Constituency>();
			while (res.next()) {
				Province p = this.locateProvince(res.getInt(2), provinces);
				Constituency c = new Constituency(res.getInt(1), p, 
						res.getString(3).trim(), res.getInt(4), false);
				constituencies.add(c);
			}
			return constituencies;
		} catch (SQLException e) {
			throw new DivsException(DivsException.ERROR_SQL,
					"Fetch constituencies:\n"+e.getMessage());
		}
	}

	/**
	 * Locate in the list of all provinces a province of certain
	 * province_id and return it 
	 * @param province_id Province id
	 * @param provinces List of provinces
	 * @return Province located in the list
	 */
	//@ pre province_id > 0;
	private /*@ pure @*/ Province locateProvince(int province_id, 
			/*@ non_null @*/ List<Province> provinces) {
		Province retval = null;
		for (int i = 0; i < provinces.size(); i++) {
			if (provinces.get(i).getProvinceId() == province_id) {
				retval = provinces.get(i);
				break;
			}
		}
		return retval;
	}

	/**
	 * Method returns a province from a certain province id
	 * @param province_id Id of a province in the database
	 * @return Province object which contains e.g. name and no of constituency seats
	 * @throws DivsException Throws exception when e.g. something is 
	 * 		wrong with db connection
	 */
	private /*@ pure @*/ Province getProvince(int province_id) throws DivsException {
		String select = "select * from Province p where province_id = ?";
		try {
			PreparedStatement pstmt = local.prepareStatement(select);
			pstmt.setInt(1, province_id);
			ResultSet res = pstmt.executeQuery();
			res.next();
			int prov_id = res.getInt("province_id"), 
				constituency_seats = res.getInt("constituency_seats"),
				additional_seats = res.getInt("additional_seats");
			String name = res.getString("name").trim();
			Province p = new Province(prov_id, name, 
					constituency_seats, additional_seats);
			return p;
		} catch (SQLException e) {
			throw new DivsException(DivsException.ERROR_SQL,
					"Fetch province:\n"+e.getMessage());
		}
	}

	/**
	 * Method returns a constituency from a certain constituency id
	 * @param constituency_id Id of a constituency in the database
	 * @return Constituency object which contains e.g. name and no of constituency seats
	 * @throws DivsException Throws exception when e.g. something is 
	 * 		wrong with db connection
	 */
	private /*@ pure @*/ Constituency getConstituency(
								int constituency_id) throws DivsException {
		String select = "select constituency_id, province_id, name, constituency_seats, bornholm " +
						"from Constituency where constituency_id = ?";
		try {
			PreparedStatement pstmt = local.prepareStatement(select);
			pstmt.setInt(1, constituency_id);
			ResultSet res = pstmt.executeQuery();
			res.next();
			int constit_id = res.getInt(1), 
				province_id = res.getInt(2),
				constituency_seats = res.getInt(4);
			String name = res.getString(3).trim();
			boolean bornholm = res.getInt(5)==1;
			Province p = this.getProvince(province_id);
			Constituency c = new Constituency(constit_id, p, name, constituency_seats, bornholm);
			return c;
		} catch (SQLException e) {
			throw new DivsException(DivsException.ERROR_SQL,
					"Fetch constituency:\n"+e.getMessage());
		}
	}

	/**
	 * Method returns a district from a certain district id
	 * @param province_id Id of a district in the database
	 * @return District with certain id
	 * @throws DivsException Throws exception when e.g. something is 
	 * 		wrong with db connection
	 */
	//@ pre district_id > 0;
	private /*@ pure @*/ District getDistrict(int district_id) throws DivsException {
		String select = "select district_id, name, constituency_id " +
						"from District where district_id = ?";
		try {
			PreparedStatement pstmt = local.prepareStatement(select);
			pstmt.setInt(1, district_id);
			ResultSet res = pstmt.executeQuery();
			res.next();
			int distr_id = res.getInt(1), 
				constit_id = res.getInt(3);
			String name = res.getString(2).trim();
			Constituency c = this.getConstituency(constit_id);
			District d = new District(distr_id, name, c);
			return d;
		} catch (SQLException e) {
			throw new DivsException(DivsException.ERROR_SQL,
					"Fetch district:\n"+e.getMessage());
		}
	}

	/**
	 * Method fetches all parties from the database
	 * @return A list of all parties
	 * @throws DivsException Throws exception when e.g. something is 
	 * 		wrong with db connection
	 */
	private /*@ pure @*/ List<Party> getParties() throws DivsException {
		String select = "select party_id, name, letter, standing from Party order by letter";
		try {
			PreparedStatement pstmt = local.prepareStatement(select);
			ResultSet res = pstmt.executeQuery();
			ArrayList<Party> parties = new ArrayList<Party>();
			while (res.next()) {
				Party p = new Party(res.getInt(1), 
						res.getString(2).trim(), res.getString(3).trim(), 
						res.getInt(4), false);
				parties.add(p);
			}
			return parties;
		} catch (SQLException e) {
			throw new DivsException(DivsException.ERROR_SQL,
					"Fetch parties:\n"+e.getMessage());
		}
	}

	/**
	 * Locate party in a list of parties
	 * @param party_id Party id
	 * @param parties List of parties
	 * @return Returns the located party. Null otherwise
	 */
	//@ pre party_id > 0;
	private /*@ pure @*/ Party locateParty(
			int party_id, /*@ non_null @*/ List<Party> parties) {
		Party retval = null;
		for (int i = 0; i < parties.size(); i++) {
			if (parties.get(i).getPartyId() == party_id) {
				retval = parties.get(i);
				break;
			}
		}
		return retval;
	}

	/**
	 * Method fetches a list of candidates from the database. Method 
	 * uses the already fetched list of parties to make references
	 * consistent
	 * @param parties List of parties already fetched in order to save some memory space
	 * @param independent Either fetch independent candidates xor candidates belonging to a party
	 * @return Returns a list of candidates
	 * @throws DivsException Throws exception when e.g. something is 
	 * 		wrong with db connection
	 */
	private /*@ pure @*/ List<Candidate> getCandidates(
			/*@ non_null @*/ List<Party> parties, boolean independent) throws DivsException {
		String select = "select candidate_id, party_id, name, cpr, position, address " +
						"from Candidate where party_id is " + (independent ? "": "not") + " null " +
						"order by party_id, candidate_id";
		try {
			PreparedStatement pstmt = local.prepareStatement(select);
			ResultSet res = pstmt.executeQuery();
			List<Candidate> candidates = new ArrayList<Candidate>();
			while (res.next()) {
				Party p = locateParty(res.getInt(2), parties);
				Candidate c = new Candidate(res.getInt(1), res.getString(3).trim(), 
						res.getString(4).trim(), p, res.getString(5).trim(), 
						res.getString(6).trim());
				candidates.add(c);
			}
			return candidates;
		} catch (SQLException e) {
			throw new DivsException(DivsException.ERROR_SQL,
					"Fetch provinces:\n"+e.getMessage());
		}
	}

	/**
	 * Method locates a certain candidate in a list
	 * @param candidate_id Candidate id of the candidate
	 * @param candidates List of candidates
	 * @return Returns a candidate (or null if not found)
	 */
	//@ pre candidate_id > 0;
	private /*@ pure @*/ Candidate locateCandidate(
			int candidate_id, /*@ non_null @*/ List<Candidate> candidates) {
		Candidate retval = null;
		for (int i = 0; i < candidates.size(); i++) {
			if (candidates.get(i).getCandidateId() == candidate_id) {
				retval = candidates.get(i);
				break;
			}
		}
		return retval;
	}

}