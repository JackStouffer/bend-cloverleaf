import createClient from "openapi-fetch";
import type { paths } from "./schema";

// The only way the frontend calls the API, so a route change in Bend that the
// frontend doesn't follow fails tsc.
export const api = createClient<paths>();
