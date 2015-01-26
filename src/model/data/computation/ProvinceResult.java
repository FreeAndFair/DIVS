package model.data.computation;

import java.util.ArrayList;
import java.util.List;

import model.data.map.Province;

/**
 * @author Ólavur Kjølbro
 */
public /*@ nullable_by_default @*/ class ProvinceResult {

	private Province province;
	private List<PartyResult> party_results;
	private int seats_taken;
	private int valid_votes;

	//@ invariant province != null;
	//@ invariant party_results != null;
	//@ invariant seats_taken >= 0;
	//@ invariant valid_votes >= 0;

	/**
	 * @param prov Province
	 */
	public ProvinceResult(/*@ non_null @*/ Province prov) {
		this.province = prov;
		party_results = new ArrayList<PartyResult>();
		this.seats_taken = 0;
		this.valid_votes = 0;
	}

	/**
	 * @return the province
	 */
	public /*@ pure @*/ Province getProvince() {
		return province;
	}

	/**
	 * @return the party_results the no of votes a certain pary has got
	 */
	public /*@ pure @*/ List<PartyResult> getPartyResult() {
		return party_results;
	}

	/**
	 * @return the seats_taken
	 */
	public /*@ pure @*/ int getAdditionalSeatsTaken() {
		return seats_taken;
	}

	/**
	 * @return the valid_votes
	 */
	public /*@ pure @*/ int getValidVotes() {
		return valid_votes;
	}

	/**
	 * @param valid_votes the valid_votes to set
	 */
	//@ pre votes >= 0;
	//@ post valid_votes == votes;
	//@ assignable valid_votes;
	public void setValidVotes(int votes) {
		this.valid_votes = votes;
	}

	/**
	 * @param seats_taken the seats_taken to set
	 */
	//@ pre seats >= 0;
	//@ post seats_taken == seats;
	//@ assignable seats_taken;
	public void setAdditionalSeatsTaken(int seats) {
		this.seats_taken = seats;
	}

	/**
	 * @param party_res the party result to set
	 */
	//@ post party_results == party_res;
	//@ assignable party_results;
	public void setPartyResult(/*@ non_null @*/ List<PartyResult> party_res) {
		this.party_results = party_res;
	}

	/**
	 * @return  A string informing about the instance
	 */
	@Override
	public /*@ pure @*/ String toString() {
		return "ProvinceResult - province: "+province.getName()+";party result size: "+party_results.size();
	}

}